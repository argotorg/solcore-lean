import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy

/-! A nested ordinary lambda retains the exact policy, compiler view and child
budget of the closure being invoked. Its Site is derived from that accepted
action and the actual native child typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)
open CallableLambdaBodyReachability

private theorem lambda_policy
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id ∧
    ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) = .ok none := by
  have sameSource : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals (context prepared named).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  constructor
  · rw [recipe.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  · intro child budget
    rw [recipe.lowerSpecial]
    unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
    have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
      unfold SourceCompilationPlan.ordinaryOwnedRequirements?
      rw [requirements, coercions]
      rfl
    have noEvidence : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized (context prepared named) child budget source scope id reasonAt
        (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
      simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions]
    simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary, Option.filter_none, noEvidence, form]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {captured : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function captured administrative)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {childFuel : Nat}
  {lowered : SourceCoreBasic.LoweredExpr}

include provenance in
theorem of_expression
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {node : ExpressionNode} {reported : Ty}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : id.occurrence.owner = function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed support.caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked function.source id = .ok (node, reported))
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody childFuel
      code.compilation code.view scope id code.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) support.caller)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    ∃ produced : Produced (compiled := compiled) support.caller.named parameters result statements sourceContext evidence
      scope (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) support.caller) id lowered,
      produced.site.code.view = code.view ∧ produced.site.code.reasonAt = code.reasonAt := by
  have nonzero : childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have viewFound := (provenance.body_view id reached).symm.trans found
  have viewRead := (CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.compatible_read_eq
    code.viewOfSource (provenance.body_view id reached)).symm.trans read
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, issued, bodyRecipe, recipe, sameCompilation⟩ := provenance.issued_recipe
  have pointwise := lambda_policy recipe viewFound form requirements coercions ordinary scope code.reasonAt
  have actualAccepted := fuelEq ▸ accepted
  rw [support.compilation] at actualAccepted
  have special : DecoratedFunctionCode.SpecialPasses code.policy code.lowerBody fuel
      (context compiled.indexed support.caller.named) code.view scope id code.reasonAt := pointwise.2 _ _
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special
    (owner.trans code.viewOfSource.owner) viewFound (pointwise.1.trans viewRead) form actualAccepted
  have hook : code.policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook
      compiled.indexed.ancestry support.caller.named.signature.key [] := by
    simpa only [support.compilation, support.active, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext] using code.expressionProfile
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      (some compiled.indexed.ancestry.graph.inputs.callable) [] := support.active ▸ code.callables
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate viewFound hook callables nativeTyped
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, _sameFuel, view, reason,
      _sourceNode, _node, _sameCertificate⟩ :=
    CallableIndexedLambdaGeneration.of_certificate compiled.indexed sourceContext evidence [] certificate actualAccepted
      profile (by rw [← support.source]; exact code.viewOfSource)
      (by rw [← support.source]; exact found) form viewFound rfl recipe.sourceCells
      (by simpa only [support.compilation, support.active, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext] using code.manifest)
      hook callables recipe.projectType native
  have issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained support.caller.named site.code := by
    apply CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes (rootFuel := rootFuel)
      compilation issued (sameBody.trans bodyRecipe) _ site.compilation
    rw [samePolicy]
    exact recipe
  let produced : Produced (compiled := compiled) support.caller.named parameters result statements sourceContext evidence
      scope (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) support.caller) id lowered := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans provenance.binder_policy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
  exact ⟨produced, view, reason⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaProducer
