import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.Staging.RecursiveScope

/-! The retained production policy supplies the recursive caller profile.
Every supported Source occurrence has genuine metadata exclusions; the actual
contextual and evidence hooks then delegate before entering their special paths.
Original Source and Code.view need separate global metadata proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {named : Named} {source : TypedSource}

private inductive SupportedForm : ExpressionForm → Prop where
  | literal {form} (atomic : CompatibleExpressionLiterals.Atomic form) : SupportedForm form
  | read (name : String) (binder : Resolved.LocalId) : SupportedForm (.reference name (.local binder))
  | group (inner : ExpressionId) : SupportedForm (.group inner)
  | tuple (ids : List ExpressionId) : SupportedForm (.tuple ids)
  | call (callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution) :
      SupportedForm (.call callee ids (.indirect metadata))

private theorem syntax_node {id : ExpressionId}
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id) :
    ∃ node, source.lookupExpression? id = some node ∧ SupportedForm node.form := by
  cases tree with
  | leaf product =>
    cases product with
    | literal found atomic => exact ⟨_, found, .literal atomic⟩
    | read found form =>
      refine ⟨_, found, ?_⟩
      rw [form]
      exact .read _ _
    | group found form _child =>
      refine ⟨_, found, ?_⟩
      rw [form]
      exact .group _
    | pair found form _first _second =>
      refine ⟨_, found, ?_⟩
      rw [form]
      exact .tuple _
  | group found form _child =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .group _
  | tuple found form _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .tuple _
  | call found form _callee _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .call _ _ _

/-- These exclusions cover every occurrence in the supported global grammar.
They contain no compiler action, runtime state or child execution law. -/
structure MetadataFor (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) : Prop where
  requirements : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → node.requirements = []
  coercions : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  localRead : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

private theorem contextual_same {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (supported : SupportedForm node.form)
    (ordinary : ∀ name binder, node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram (context prepared named).plan
      prepared.base.locals (context prepared named).owner none source id = .ok source := by
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic =>
    cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  | read name binder =>
    unfold SourceCoreGeneralFunctions.contextualSource
    rw [found]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [form]
    dsimp only
    rw [ordinary name binder form]
    rfl
  | group => simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  | tuple => simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  | call => simp [SourceCoreGeneralFunctions.contextualSource, found, form]

private theorem evidence_none
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (current : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) {id : ExpressionId} {node : ExpressionNode}
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    (found : source.lookupExpression? id = some node) (supported : SupportedForm node.form)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller current child budget
      source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic =>
    cases atomic <;>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
  | read =>
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
  | group =>
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
  | tuple =>
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
  | call callee ids metadata =>
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      arguments callee ids metadata form]

private theorem special_none
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    (metadata : MetadataFor prepared named source)
    {id : ExpressionId}
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id tree node found)
  have noEvidence := evidence_none prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized (context prepared named) child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found supported
    (metadata.requirements id tree node found) (metadata.coercions id tree node found)
    (metadata.arguments id tree node found)
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | group => rfl
  | tuple => rfl
  | call => rfl

theorem recipe_policy_for
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy (context prepared named)
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt := by
  constructor
  · intro id tree child budget
    rw [recipe.lowerSpecial]
    exact special_none compilation rootFuel metadata tree child budget scope reasonAt
  · intro id tree
    obtain ⟨node, found, supported⟩ := syntax_node tree
    have sameSource := contextual_same found supported (metadata.localRead id tree node found)
    rw [recipe.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  · exact recipe.lowerRead
  · exact recipe.leafLowerer

/-- The full profile is proved from one actual retained production recipe.
The independent raw typing, scope declarations and CallsReady remain separate. -/
theorem retained_policy_for
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : MetadataFor prepared named source)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact recipe_policy_for recipe metadata scope reasonAt

/-- Original and viewed Sources each retain the global Syntax quantifier.
Reached-node metadata transport alone does not discharge either global input. -/
theorem retained_paired_policy_for
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (original : MetadataFor prepared named function.source)
    (viewed : MetadataFor prepared named code.view)
    (originalScope viewScope : SourceCoreLocalCell.Scope)
    (originalReasonAt viewReasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) function.source originalScope originalReasonAt ∧
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) code.view viewScope viewReasonAt :=
  ⟨retained_policy_for retained original originalScope originalReasonAt,
    retained_policy_for retained viewed viewScope viewReasonAt⟩

/-- Registry provenance transports the full original Source profile to every
actual selected invocation scope, without changing its global Syntax quantifier. -/
theorem retained_selected_policy_for
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : MetadataFor prepared named function.source)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure function child)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) child.source scope reasonAt := by
  rw [stages.source selected]
  exact retained_policy_for retained metadata scope reasonAt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles
