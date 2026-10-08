import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles

/-! Genuine extra leaves use the actual root policy at each child fuel.
Lambda joint bodies and indirect children retain their literal compiler factory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedPreparedOrdinaryLambdaFormation
open CallableIndexedOwnedContextualCompilerPolicyProfiles

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The same-policy certificate chooses one Site, whose genuine dependent
collector inputs build its joint body. The root policy is never reselected. -/
theorem lambda_of_accepted
    {childFuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source caller.named) view)
    (sourceFound : (source caller.named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result statements)
    (rawType : sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements sourceContext evidence []))
    (rawOrdinary : Dynamic.OrdinaryRequirementLayout sourceNode.requirements sourceNode.coercions [])
    (rawCoercions : sourceNode.coercions = [])
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (siteInputs : ∀ produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered,
      produced.diagnostics = diagnostics → produced.namedCode = namedCode → HEq produced.compilation compilation →
      produced.site.code.policy = root.selected.policy → produced.site.code.lowerBody = root.selected.lowerBody →
      produced.site.code.fuel = childFuel → produced.site.code.view = view → produced.site.code.reasonAt = reasonAt →
      Nonempty (CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller produced)) :
    ∃ certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) view scope id node parameters result statements reported reasonAt lowered,
      ∃ receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
          sourceContext evidence scope id lowered,
        receipt.formation.produced.site.code.policy = root.selected.policy ∧
        receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody ∧
        receipt.formation.produced.site.code.fuel = childFuel ∧
        receipt.formation.produced.site.code.view = view ∧
        receipt.formation.produced.site.code.reasonAt = reasonAt ∧
        HEq receipt.formation.produced.site.code.receipt certificate := by
  have pointwise := lambda_policy root (scope := scope) (reasonAt := reasonAt) found (form.trans sourceForm) requirements coercions ordinary
  have special : DecoratedFunctionCode.SpecialPasses root.selected.policy root.selected.lowerBody childFuel
      (context compiled.indexed caller.named) view scope id reasonAt := by
    exact pointwise.special _ _
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special owner found
    (pointwise.read.trans read) (form.trans sourceForm) accepted
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, sameFuel, sameView, sameReason, sameSourceNode,
      _sameNode, sameCertificate⟩ :=
    of_certificate compiled.indexed sourceContext evidence [] certificate accepted profile viewOfSource sourceFound
      sourceForm found form root.sourceCells root.rawLambdaBody root.rawLambdaExpression root.callables root.projectType typed
  let produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered :=
    ⟨diagnostics, namedCode, compilation, site, identifier, emitted,
      (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans root.selected.binder,
      sameBody.trans root.selected.recipe⟩
  obtain ⟨inputs⟩ := siteInputs produced rfl rfl (HEq.refl compilation) samePolicy sameBody sameFuel sameView sameReason
  obtain ⟨body, _entry, _readFuel⟩ := at_site produced.compilation produced.site produced.recipe
    (Program.ofChecked compiled.sourceProgram) inputs.entry inputs.frame inputs.expressionSyntax inputs.certificates
    inputs.readFuel inputs.diagnosticPolicy inputs.issued.invalidOperand inputs.issued.invalidUnary
    inputs.issued.invalidProjection inputs.issued.missingDefault inputs.edited inputs.avoids inputs.unique
    inputs.sameLedger inputs.syntaxTransport inputs.expressions inputs.syntaxTree inputs.viewSyntax inputs.projection
    inputs.static inputs.nativeTyped
  let formation : Formation caller sourceContext evidence scope id lowered := {
    parameters := parameters, result := result, statements := statements, produced := produced
    expressionSyntax := inputs.expressionSyntax, certificates := inputs.certificates, issued := inputs.issued
    diagnosticPolicy := inputs.diagnosticPolicy, body := body
    sourceType := sameSourceNode ▸ rawType, ordinary := sameSourceNode ▸ rawOrdinary, coercions := sameSourceNode ▸ rawCoercions }
  let receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
      sourceContext evidence scope id lowered := ⟨formation, rfl, rfl, HEq.refl compilation⟩
  exact ⟨certificate, receipt, samePolicy, sameBody, sameFuel, sameView, sameReason, sameCertificate⟩

/-- The actual indirect invocation retains the physical children, raw row and
prepared callsite under the same root policy at its child fuel. -/
theorem indirect_of_accepted
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
      source sourceContext evidence scope administrative certificates)
    {childFuel : Nat} {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (typed : ExpressionHasType source sourceContext id node.type) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) source scope id reasonAt = .ok lowered) :
    Nonempty (CallableIndexedOwnedIndirectCompilerReceipts.Receipt compiled.indexed.ancestry.graph.inputs.callable [] factory
      (policy := root.selected.policy) (body := root.selected.lowerBody) (fuel := childFuel)
      (id := id) (callee := callee) (ids := ids) (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered)) := by
  have pointwise := indirect_policy root (scope := scope) (reasonAt := reasonAt) found form requirements coercions arguments ordinary
  exact CallableIndexedOwnedIndirectCompilerReceipts.Receipt.of_functions factory _ [] found form typed unique
    pointwise.special pointwise.read root.callables accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
