import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryExpressionProfile
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds

/-! A finite ordinary expression tree inside an actually materialized lambda obtains its
static certificate from that lambda's contextual compiler. Finite metadata
checks select the ordinary branch; no expression or body law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionCertificate
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation
open GeneralizedLocalInstanceCompilation (Inputs)

abbrev Site (inputs : Inputs) (source : TypedSource) (id : ExpressionId) :=
  GeneralizedLocalOrdinaryExpressionProfile.Site inputs.locals inputs.current.owner source id

abbrev site? (inputs : Inputs) (source : TypedSource) (id : ExpressionId) :=
  GeneralizedLocalOrdinaryExpressionProfile.site? inputs.locals inputs.current.owner source id

private theorem contextual {inputs : Inputs} {source : TypedSource} {id : ExpressionId}
    (site : Site inputs source id) (parent : Option SourceCoreLocalEvidence.Prepared) :
    SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
      inputs.current.owner parent source id = .ok source := by
  have supported := site.form
  generalize shape : site.node.form = form at supported
  cases supported with
  | literal atomic => cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, site.found, shape]
  | read name binder =>
    have ordinary := site.ordinary name binder shape
    simp only [SourceCoreGeneralFunctions.contextualSource, site.found, bind, Except.bind, pure, Except.pure,
      shape, ordinary, Bool.false_eq_true, ↓reduceIte]
  | group inner | pair left right => simp [SourceCoreGeneralFunctions.contextualSource, site.found, shape]

private theorem special {inputs : Inputs} {source : TypedSource} {id : ExpressionId}
    (site : Site inputs source id) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    GeneralizedLocalLambdaCompilation.special inputs prepared fuel
      (GeneralizedLocalLambdaCompilation.context inputs prepared) child budget source scope id reasonAt = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? site.node = some site.node.requirements := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [site.coercions]
    change (if site.node.requirements.length < 0 then none else
      if site.node.requirements = site.node.requirements.take (site.node.requirements.length - 0) ++ [] then
        some (site.node.requirements.take (site.node.requirements.length - 0)) else none) = some site.node.requirements
    simp
  have evidence : SourceCoreEvidence.lowerWithProjector inputs.program
      (GeneralizedLocalLambdaCompilation.representation inputs prepared).expressions.projectType
      prepared.caller (GeneralizedLocalLambdaCompilation.context inputs prepared) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution) = .ok none := by
    have supported := site.form
    have requirements := site.requirements
    generalize shape : site.node.form = form at supported requirements
    cases supported with
    | literal atomic =>
      cases atomic with
      | integer literal resolution =>
        simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, site.coercions]
      | unit | bool name value | word literal =>
        simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions]
    | read name binder | group inner | pair left right =>
      simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions]
  have noInitializer : inputs.locals.bindings.find? (fun binding =>
      decide (binding.caller = (GeneralizedLocalLambdaCompilation.context inputs prepared).owner ∧ binding.initializer = id)) = none :=
    site.notInitializer
  unfold GeneralizedLocalLambdaCompilation.special
  change (do
    let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
      inputs.current.owner (some prepared) source id
    _) = .ok none
  rw [contextual site]
  simp only [bind, Except.bind, pure, Except.pure, site.found, noInitializer, Option.filter_none]
  rw [evidence]
  have supported := site.form
  generalize shape : site.node.form = form at supported
  cases supported with
  | literal atomic => cases atomic <;> simp
  | read name binder =>
    simp only
    have noGeneralized : inputs.locals.bindings.any (fun binding =>
        decide (binding.caller = (GeneralizedLocalLambdaCompilation.context inputs prepared).owner ∧ binding.binder.id = binder)) = false :=
      site.ordinary name binder shape
    rw [noGeneralized]
    rfl
  | group inner | pair left right => simp

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
    (tree : GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view id)
    (unique : NodeOccurrencesUnique material.code.view)
    (declarations : CompatibleExpressionReads.ScopeDeclarations material.code.view scope context)
    {node : ExpressionNode} (found : material.code.view.lookupExpression? id = some node)
    (typed : ExpressionHasType material.code.view context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody fuel
      material.code.compilation material.code.view scope id reasonAt = .ok lowered) :
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view context material.code.compilation.solvedRequirements
      reasonAt scope id lowered := by
  obtain ⟨site⟩ := tree.site
  let allowed := GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view
  have policies : CompatibleExpressionProducts.PolicyOn material.code.policy material.code.compilation compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view scope reasonAt allowed := by
    constructor
    · intro child admitted shape compiler budget
      obtain ⟨childSite⟩ := admitted.site
      exact (policy_on material childSite (scope := scope) (reasonAt := reasonAt)).special child rfl shape compiler budget
    · intro child admitted shape
      obtain ⟨childSite⟩ := admitted.site
      exact (policy_on material childSite (scope := scope) (reasonAt := reasonAt)).read child rfl shape
    · exact (policy_on material site (scope := scope) (reasonAt := reasonAt)).lower
    · exact (policy_on material site (scope := scope) (reasonAt := reasonAt)).leaf
  apply CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on unique declarations
    policies (fun admitted found member => admitted.children found member) ?_ tree.syntax tree found typed accepted
  intro child childNode admitted _ childFound
  obtain ⟨childSite⟩ := admitted.site
  exact Option.some.inj (childSite.found.symm.trans childFound) ▸ childSite.coercions

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionCertificate
