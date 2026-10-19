import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (SupportedForm syntax_node contextual_same evidence_none)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt Supported Child)
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named} {source : TypedSource}
  {directSites : DeclarationInstantiation → Prop} {allowed : ExpressionId → Prop}

structure MetadataOn (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : Named) (source : TypedSource) (allowed : ExpressionId → Prop) (directSites : DeclarationInstantiation → Prop) : Prop where
  requirements : ∀ id, allowed id → GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node →
    node.requirements = [] ∨ (∃ literal resolution, node.form = .integerLiteral literal resolution) ∨
      (∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation)) ∨ OperatorForm node.form
  coercions : ∀ id, allowed id → GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, allowed id → GeneralSyntax source id directSites →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, allowed id → GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  localRead : ∀ id, allowed id → GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

theorem MetadataFor.on (metadata : MetadataFor prepared named source directSites)
    (allowed : ExpressionId → Prop) : MetadataOn prepared named source allowed directSites :=
  ⟨fun id _ => metadata.requirements id, fun id _ => metadata.coercions id,
    fun id _ => metadata.initializer id, fun id _ => metadata.arguments id, fun id _ => metadata.localRead id⟩

theorem MetadataOn.non_direct_requirements (metadata : MetadataOn prepared named source allowed directSites)
    {id : ExpressionId} (permitted : allowed id) (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect) (primitive : tree.NonOperator)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution := by
  rcases metadata.requirements id permitted tree node found with empty | literal | ⟨callee, ids, instantiation, form⟩ | operator
  · exact .inl empty
  · exact .inr literal
  · exact False.elim (ordinary node found callee ids instantiation form)
  · exact False.elim (primitive node found operator)

/-- The original contextual step agrees with the actual evidence lowerer at a
named declaration call. No second compiler policy is selected. -/
theorem direct_hook_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataOn prepared named source allowed directSites)
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (permitted : allowed id) (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  have same := contextual_same found (form ▸ SupportedForm.direct callee ids instantiation)
    (metadata.localRead id permitted tree node found)
  rw [recipe.lowerSpecial]
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [same, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id permitted tree, Option.filter_none]
  cases actual : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
  | error error => rfl
  | ok output => cases output <;> simp [form]

theorem special_none_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    (metadata : MetadataOn prepared named source allowed directSites)
    {id : ExpressionId} (permitted : allowed id) (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect) (primitive : tree.NonOperator)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id permitted tree node found)
  have noEvidence := evidence_none prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized (context prepared named) child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found supported
    (metadata.non_direct_requirements permitted tree ordinary primitive found) (metadata.coercions id permitted tree node found)
    (metadata.arguments id permitted tree node found)
    (fun callee ids instantiation form => False.elim (ordinary node found callee ids instantiation form))
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id permitted tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id permitted tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | proxy | index | unary | binary | conditional | group | constructor | direct | builtin => rfl
  | tuple => rfl
  | call => rfl

theorem read_policy_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataOn prepared named source allowed directSites)
    {id : ExpressionId} (permitted : allowed id) (tree : GeneralSyntax source id directSites) :
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id permitted tree node found)
  rw [recipe.readExpression]
  simp only [sameSource, bind, Except.bind]
  rfl

theorem reads_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataOn prepared named source allowed directSites) :
    CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport.ReadPolicyOn policy prepared.fuel
      (.initial checked) source allowed directSites :=
  ⟨fun _ permitted tree => read_policy_on recipe metadata permitted tree, recipe.lowerRead, recipe.leafLowerer⟩

theorem viewed_metadata {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (original : MetadataFor prepared named source directSites) :
    MetadataOn prepared named view (fun id => Reaches view roots (.expression id)) directSites := by
  have originalTree : ∀ id, Reaches view roots (.expression id) →
      GeneralSyntax view id directSites → GeneralSyntax source id directSites := fun id reached tree =>
    syntax_original edited avoids tree (reached.metadata edited.metadata.symm)
  have lookup : ∀ id, Reaches view roots (.expression id) → ∀ node,
      view.lookupExpression? id = some node → source.lookupExpression? id = some node :=
    fun id reached node found => (expression_lookup edited avoids (reached.metadata edited.metadata.symm)).trans found
  exact {
    requirements := fun id reached tree node found => original.requirements id (originalTree id reached tree) node (lookup id reached node found)
    coercions := fun id reached tree node found => original.coercions id (originalTree id reached tree) node (lookup id reached node found)
    initializer := fun id reached tree => original.initializer id (originalTree id reached tree)
    arguments := fun id reached tree node found => original.arguments id (originalTree id reached tree) node (lookup id reached node found)
    localRead := fun id reached tree node found => original.localRead id (originalTree id reached tree) node (lookup id reached node found) }

theorem operator_hook_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataOn prepared named source allowed directSites)
    {id : ExpressionId}
    {node : ExpressionNode} (permitted : allowed id) (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : (∃ operator operand, node.form = .unary operator operand) ∨
      (∃ operator left right, node.form = .binary left operator right))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  rcases form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
  all_goals
   have supported : SupportedForm node.form := by rw [form]; first | exact .unary _ _ | exact .binary _ _ _
   have same := contextual_same found supported (metadata.localRead id permitted tree node found)
   rw [recipe.lowerSpecial]
   unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
   simp only [same, bind, Except.bind, found, pure, Except.pure,
     metadata.initializer id permitted tree, Option.filter_none]
   cases actual : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
       ((representation prepared).atContext named.signature.key []).expressions.projectType
       named.specialized (context prepared named) child budget source scope id reasonAt
       (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
   | error error => rfl
   | ok output => cases output <;> simp [form]


section Retained
variable {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
  (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
  (metadata : MetadataFor prepared named source directSites)

include retained metadata in
theorem retained_policy_for
    (callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
    (supported : ∀ instantiation, directSites instantiation → Supported code.compilation.plan instantiation)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    MethodStepPolicyFor code.policy code.compilation prepared.fuel (.initial checked) source scope reasonAt directSites := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation] at supported ⊢
  exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    recipe callables supported metadata scope reasonAt

include retained metadata in
theorem retained_read_policy {id : ExpressionId} (tree : GeneralSyntax source id directSites) :
    code.policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, _sameCompilation⟩ := retained
  exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy recipe metadata tree

include retained metadata in
theorem retained_direct_hook
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match code.policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower code.compilation child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized code.compilation child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.direct_hook
    recipe metadata tree found form child budget scope reasonAt

include retained metadata in
theorem retained_accepted_direct_action
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (fuel + 1)
      code.compilation source scope id reasonAt = .ok lowered) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized code.compilation (Child code.policy code.lowerBody fuel code.compilation)
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none ∨
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized code.compilation (Child code.policy code.lowerBody fuel code.compilation)
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok (some lowered) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation] at accepted ⊢
  exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.accepted_direct_action
    recipe metadata tree found form accepted
include retained metadata in
theorem retained_operator_hook
    {id : ExpressionId}
    {node : ExpressionNode} (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : (∃ operator operand, node.form = .unary operator operand) ∨
      (∃ operator left right, node.form = .binary left operator right))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match code.policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower code.compilation child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized code.compilation child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.operator_hook
    recipe metadata tree found form child budget scope reasonAt

end Retained

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
