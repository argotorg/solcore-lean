import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryReadSite
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds

/-! An ordinary local read inside an actually materialized lambda obtains its
static certificate from that lambda's contextual compiler. Finite metadata
checks select the ordinary branch; no expression or body law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadCertificate
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation
open GeneralizedLocalInstanceCompilation (Inputs)

abbrev Site (inputs : Inputs) (source : TypedSource) (id : ExpressionId) :=
  GeneralizedLocalOrdinaryReadSite.Observations inputs.locals inputs.current.owner source id

abbrev site? (inputs : Inputs) (source : TypedSource) (id : ExpressionId) :=
  GeneralizedLocalOrdinaryReadSite.observations? inputs.locals inputs.current.owner source id

private theorem contextual {inputs : Inputs} {source : TypedSource} {id : ExpressionId}
    (site : Site inputs source id) (parent : Option SourceCoreLocalEvidence.Prepared) :
    SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
      inputs.current.owner parent source id = .ok source := by
  simp only [SourceCoreGeneralFunctions.contextualSource, site.found, bind, Except.bind, pure, Except.pure,
    site.form, site.ordinary, Bool.false_eq_true, ↓reduceIte]

private theorem special {inputs : Inputs} {source : TypedSource} {id : ExpressionId}
    (site : Site inputs source id) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    GeneralizedLocalLambdaCompilation.special inputs prepared fuel
      (GeneralizedLocalLambdaCompilation.context inputs prepared) child budget source scope id reasonAt = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? site.node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [site.requirements, site.coercions]
    rfl
  have evidence : SourceCoreEvidence.lowerWithProjector inputs.program
      (GeneralizedLocalLambdaCompilation.representation inputs prepared).expressions.projectType
      prepared.caller (GeneralizedLocalLambdaCompilation.context inputs prepared) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution) = .ok none := by
    simp [SourceCoreEvidence.lowerWithProjector, site.found, site.form, ordinary,
      site.requirements, site.coercions]
  have noInitializer : inputs.locals.bindings.find? (fun binding =>
      decide (binding.caller = (GeneralizedLocalLambdaCompilation.context inputs prepared).owner ∧ binding.initializer = id)) = none :=
    site.notInitializer
  have noGeneralized : inputs.locals.bindings.any (fun binding =>
      decide (binding.caller = (GeneralizedLocalLambdaCompilation.context inputs prepared).owner ∧ binding.binder.id = site.binder)) = false :=
    site.ordinary
  unfold GeneralizedLocalLambdaCompilation.special
  change (do
    let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
      inputs.current.owner (some prepared) source id
    _) = .ok none
  rw [contextual site]
  simp only [bind, Except.bind, pure, Except.pure, site.found,
    noInitializer, Option.filter_none]
  rw [evidence]
  simp only [site.form, noGeneralized, Bool.false_eq_true, ↓reduceIte]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  {id : ExpressionId} (site : Site material.inputs material.code.view id)

include site in
/-- The actual prepared representation supplies both the read callback and the
ordinary branch of the contextual override at this exact Source occurrence. -/
theorem policy_on {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word} :
    CompatibleExpressionProducts.PolicyOn material.code.policy material.code.compilation compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view scope reasonAt (fun child => child = id) := by
  constructor
  · intro child same _ childCompiler budget
    subst child
    rw [material.policy, material.compilation]
    exact special site material.packet.original.emission.prepared material.packet.fuel childCompiler budget scope reasonAt
  · intro child same _
    subst child
    rw [material.policy]
    change (do
      let source ← SourceCoreGeneralFunctions.contextualSource material.inputs.program material.inputs.current.plan
        material.inputs.locals material.inputs.current.owner (some material.packet.original.emission.prepared)
        material.code.view id
      _) = _
    rw [contextual site]
    simp only [bind, Except.bind]
    unfold GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl
  · rw [material.policy]
    unfold GeneralizedLocalLambdaCompilation.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl
  · rw [material.policy]
    unfold GeneralizedLocalLambdaCompilation.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl

theorem of_accepted {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique material.code.view)
    (declarations : CompatibleExpressionReads.ScopeDeclarations material.code.view scope context)
    (typed : ExpressionHasType material.code.view context id site.node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody fuel
      material.code.compilation material.code.view scope id reasonAt = .ok lowered) :
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view context material.code.compilation.solvedRequirements
      reasonAt scope id lowered := by
  apply CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on unique declarations
    (policy_on material site) ?_ ?_ (.read site.found site.form) rfl site.found typed accepted
  · intro parent node child same found member
    subst parent
    have nodeEq := Option.some.inj (site.found.symm.trans found)
    subst node
    simp [site.form, ExpressionForm.references] at member
  · intro child node same _ found
    subst child
    have nodeEq := Option.some.inj (site.found.symm.trans found)
    exact nodeEq ▸ site.coercions

/-- The actual reference form selects the read leaf of the finite compiler
certificate, so body execution needs no generic child or literal law. -/
theorem lowered_read {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique material.code.view)
    (declarations : CompatibleExpressionReads.ScopeDeclarations material.code.view scope context)
    (typed : ExpressionHasType material.code.view context id site.node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody fuel
      material.code.compilation material.code.view scope id reasonAt = .ok lowered) :
    CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
      material.code.view context reasonAt scope id lowered := by
  obtain ⟨tree, sites⟩ := of_accepted material site unique declarations typed accepted
  clear sites
  cases tree with
  | read receipt => exact receipt
  | literal receipt =>
    obtain ⟨node, found, literal⟩ := receipt
    have same := Option.some.inj (found.symm.trans site.found)
    subst node
    generalize lowered.type = nativeType at literal
    generalize lowered.expression = nativeCode at literal
    cases literal with
    | unit form _ _ _ | bool _ form _ _ _ | word _ form _ _ _ _
    | resolvedWord form _ | resolvedInteger form _ =>
      rw [site.form] at form
      cases form
  | group metadata form _ _ _ | pair metadata form _ _ _ _ _ =>
    have same := Option.some.inj (metadata.found.symm.trans site.found)
    cases same
    rw [site.form] at form
    cases form

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadCertificate
