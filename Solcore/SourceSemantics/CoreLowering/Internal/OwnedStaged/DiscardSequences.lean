import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardTerminals
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.CallableOrdinaryPreparedScopeAnnotationCallsReady

/-!
# Staged bounds: discard sequences

Bodies with discards before a terminal: compiler support and factories, body and lambda bounds, and the policies and readiness of ordinary rows.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryEvidencePolicy
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryEvidencePolicy
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (SupportedForm syntax_node contextual_same evidence_none)
open CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles (MetadataFor)
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
      ∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation)
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
    {id : ExpressionId} (permitted : allowed id) (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution := by
  rcases metadata.requirements id permitted tree node found with empty | literal | ⟨callee, ids, instantiation, form⟩
  · exact .inl empty
  · exact .inr literal
  · exact False.elim (ordinary node found callee ids instantiation form)

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
    {id : ExpressionId} (permitted : allowed id) (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect)
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
    (metadata.non_direct_requirements permitted tree ordinary found) (metadata.coercions id permitted tree node found)
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
    StepPolicyFor code.policy code.compilation prepared.fuel (.initial checked) source scope reasonAt directSites := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation] at supported ⊢
  exact CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.recipe_policy_for
    recipe callables supported metadata scope reasonAt

include retained metadata in
theorem retained_read_policy {id : ExpressionId} (tree : GeneralSyntax source id directSites) :
    code.policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, _sameCompilation⟩ := retained
  exact CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.read_policy recipe metadata tree

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
  exact CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.direct_hook
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
  exact CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.accepted_direct_action
    recipe metadata tree found form accepted
end Retained

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryEvidencePolicy
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport
/-! Every ordered child of the same sequence receipt is issued from genuine
 original raw typing and its actual accepted compiler action. The constructive
 view transport retains full reached metadata and production callable policy.
 Original body typing proves the final raw result before whole-body assembly.
 Static CallsReady is indexed by the exact issued proof; no meaning is stored.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts (FlowReceipt Receipt)
open CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds (Tree)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyOn Certificate)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditionsOn)

private theorem tree_nonempty {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {result : Ty} {rawResult : TypeSystem.Ty} {statements : List StatementId} {flow : Expr}
    (tree : Tree compiled context invocation scope semanticFaults result rawResult statements flow) :
    statements ≠ [] := by
  cases tree with
  | terminal root head sameType sameRaw => cases head <;> simp
  | discard root contains form tail => simp

/-- Full original typing fixes the raw result of any actual issued tree.
The native child type and metadata view are not used to infer this equality. -/
theorem raw_result {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context final : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {result : Ty} {rawResult expected : TypeSystem.Ty} {facts : BodyFacts}
    {statements : List StatementId} {flow : Expr}
    (unique : NodeOccurrencesUnique invocation.source)
    (tree : Tree compiled context invocation scope semanticFaults result rawResult statements flow)
    (typed : StatementsHaveType invocation.source { returnType := expected }
      context statements final facts)
    (completes : BodyCompletes expected facts) : rawResult = expected := by
  induction tree generalizing final facts with
  | terminal root head sameType sameRaw =>
    obtain ⟨node, found, resultType, childTyped⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head typed completes
    have nodeEq : root.support.node = node :=
      Option.some.inj (root.support.found.symm.trans found)
    exact sameRaw.symm.trans ((congrArg ExpressionNode.type nodeEq).trans resultType)
  | discard root contains form tail ih =>
    obtain ⟨firstType, tailFacts, firstTyped, remaining, tailCompletes⟩ :=
      CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.discard_tail_typed
        unique contains form (tree_nonempty tail) typed completes
    exact ih remaining tailCompletes

private theorem tree_of_roots {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {policy : SourceCoreLoops.Policy} {view : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView invocation.source view)
    (roots : ∀ expression child, receipt.Children expression child →
      Nonempty (RootAt compiled context invocation scope expression child semanticFaults)) :
    ∃ rawResult, Nonempty (Tree compiled context invocation scope semanticFaults result rawResult
      statements flow) := by
  revert roots
  induction receipt with
  | terminal terminal generated =>
    intro roots
    obtain ⟨root⟩ := roots _ _ ⟨rfl, rfl⟩
    exact ⟨root.support.node.type, ⟨.terminal root
      (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head terminal metadata)
      terminal.sameType rfl⟩⟩
  | discard found form first generated tail accepted ih =>
    intro roots
    obtain ⟨root⟩ := roots _ _ (.inl ⟨rfl, rfl⟩)
    obtain ⟨rawResult, ⟨tailTree⟩⟩ := ih (fun expression child used =>
      roots expression child (.inr used))
    exact ⟨rawResult, ⟨.discard root (lookupStatement?_sound (metadata.statement found)) form tailTree⟩⟩

private theorem child_generated {policy : SourceCoreLoops.Policy} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    {expression : ExpressionId} {child : SourceCoreBasic.LoweredExpr}
    (used : receipt.Children expression child) :
    ∃ childFuel, policy.lowerExpression childFuel view scope expression reasonAt = .ok child := by
  revert used
  induction receipt with
  | terminal terminal generated =>
    intro used
    rcases used with ⟨rfl, rfl⟩
    exact ⟨terminal.childFuel, terminal.generated⟩
  | discard found form first generated tail accepted ih =>
    intro used
    rcases used with ⟨rfl, rfl⟩ | tailUsed
    · exact ⟨_, generated⟩
    · exact ih tailUsed

section Static
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {statementPolicy : SourceCoreLoops.Policy} {fuel : Nat} {view : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {result : Ty}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {bodyCode : Expr}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {invocation : Staging.Recursive.Scope} {changed : List ExpressionId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {semanticFaults : FunctionCalls.FaultRep}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}

/-- The same original frame and accepted receipt cover all actual children.
The compiler recipe, policy, declarations and static call authority stay real. -/
structure Static (receipt : Receipt statementPolicy fuel view scope statements result
    reasonAt fellThrough escaped bodyCode) where
  edited : LocalView invocation.source view changed
  avoids : Avoids invocation.source (statements.map NodeId.statement) changed
  sourceProfile : PolicyOn policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source scope reasonAt
      (fun id => Reaches invocation.source (statements.map NodeId.statement) (.expression id))
  viewProfile : PolicyOn policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) view scope reasonAt
      (fun id => Reaches view (statements.map NodeId.statement) (.expression id))
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active
  expressionCallback : statementPolicy.lowerExpression = fun childFuel source current id token =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min childFuel bodyFuel)
      compilation source current id token
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  parameters : MonoBindersExtend function.source.owner function.context function.parameters types context
  sameSource : invocation.source = function.source
  body : function.body = statements
  syntaxTree : ∀ expression child, receipt.tree.Children expression child → Syntax view expression
  conditions : OriginalConditionsOn compiled policy compilation readFuel context invocation
    reasonAt scope (statements.map NodeId.statement) semanticFaults

variable {receipt : Receipt statementPolicy fuel view scope statements result reasonAt
    fellThrough escaped bodyCode}
  (packet : Static (compiled := compiled) (function := function) (context := context)
    (types := types) (invocation := invocation) (changed := changed)
    (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
    (native := native) (active := active) receipt)
include packet

private theorem original_available (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr)
    (used : receipt.tree.Children expression child) :
    (invocation.source.lookupExpression? expression).isSome := by
  obtain ⟨node, found, typed⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.at_parameters receipt.tree
      packet.edited.metadata packet.frame packet.parameters packet.sameSource packet.body
      expression child used
  exact Option.isSome_of_eq_some found

/-- The actual lookup selects data; frame-derived existence supplies its proof. -/
def Static.originalNode (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr)
    (used : receipt.tree.Children expression child) : ExpressionNode :=
  (invocation.source.lookupExpression? expression).get (original_available packet expression child used)

/-- Each child's original raw type is its own actual stored node type. -/
def Static.authority (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr)
    (used : receipt.tree.Children expression child) :
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.OriginalAuthority
      compiled policy compilation readFuel context invocation reasonAt scope expression
      (packet.originalNode expression child used).type semanticFaults := by
  let node := packet.originalNode expression child used
  have found : invocation.source.lookupExpression? expression = some node :=
    Option.eq_some_of_isSome (original_available packet expression child used)
  have typed : ExpressionHasType invocation.source context expression node.type := by
    obtain ⟨original, originalFound, originalTyped⟩ :=
      CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.at_parameters receipt.tree
        packet.edited.metadata packet.frame packet.parameters packet.sameSource packet.body
        expression child used
    have same : original = node := Option.some.inj (originalFound.symm.trans found)
    simpa only [same] using originalTyped
  exact CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.original_authority_on
    packet.conditions
    (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
      receipt.tree packet.edited.metadata expression child used) ⟨node, found, rfl, typed⟩

private theorem view_action {expression : ExpressionId} {child : SourceCoreBasic.LoweredExpr}
    (used : receipt.tree.Children expression child) :
    ∃ childFuel, SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody
      (min childFuel bodyFuel) compilation view scope expression reasonAt = .ok child := by
  obtain ⟨childFuel, generated⟩ := child_generated receipt.tree used
  exact ⟨childFuel, by simpa only [packet.expressionCallback] using generated⟩

/-- Constructive full-node action transport precedes the genuine331 extractor. -/
theorem Static.certificate (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr)
    (used : receipt.tree.Children expression child) :
    Certificate policy lowerBody compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression child := by
  obtain ⟨childFuel, generated⟩ := view_action packet used
  exact CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate_on
    packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
    (packet.syntaxTree expression child used)
    (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
      receipt.tree packet.edited.metadata expression child used)
    (packet.authority expression child used) generated

/-- CallsReady belongs to every exact internally issued used-child proof. -/
structure Ready : Prop where
  calls : ∀ expression child (used : receipt.tree.Children expression child),
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) (packet.certificate expression child used)

/-- Existence packaging keeps each actual child fuel; no Type chooser is exposed. -/
theorem Static.root (ready : Ready packet) (expression : ExpressionId)
    (child : SourceCoreBasic.LoweredExpr) (used : receipt.tree.Children expression child) :
    Nonempty (RootAt compiled context invocation scope expression child semanticFaults) := by
  obtain ⟨childFuel, generated⟩ := view_action packet used
  exact ⟨CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_view_action_on
    packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
    (packet.syntaxTree expression child used)
    (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
      receipt.tree packet.edited.metadata expression child used)
    (packet.authority expression child used) generated (ready.calls expression child used)⟩

/-- Original full body typing aligns the internally issued sequence tree with
its declaration's raw result at the actual parameter context and chosen scope. -/
theorem issued_tree (ready : Ready packet) :
    Nonempty (Tree compiled context invocation scope semanticFaults result function.resultType
      statements receipt.flow) := by
  obtain ⟨rawResult, ⟨tree⟩⟩ := tree_of_roots receipt.tree packet.edited.metadata
    (fun expression child used => packet.root ready expression child used)
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters packet.frame packet.parameters
  rw [packet.body, ← packet.sameSource] at typed
  have sameRaw : rawResult = function.resultType :=
    raw_result packet.conditions.unique tree typed completes
  subst rawResult
  exact ⟨tree⟩
end Static
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds
/-! Whole-body assembly for the literal recursive discard sequence. Original
full body typing fixes its declared raw result, then strict numeric Root IHs
construct the reached flow. The same accepted receipt supplies one finish
footer. No execution law or desired completed result is a static input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Sequence SequenceSupport parameterScope)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts (FlowReceipt Receipt)
open CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds (Tree)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
open CallableIndexedOwnedPreparedStagedTerminalBodyMeaning (fallback)

/-- The retained accepted statement action fixes the complete renamed footer. -/
theorem emitted_rename {policy : SourceCoreLoops.Policy} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope statements result reasonAt fellThrough escaped code)
    (ξ : Renaming) :
    code.rename ξ = CallableIndexedOwnedAdmittedStagedTerminalBody.code result
      (receipt.flow.rename ξ) escaped ((fallback result fellThrough).rename ξ) := by
  have footer := congrArg (fun generated : Expr => generated.rename ξ) receipt.emitted
  exact footer.trans (by
    simpa only [CompatibleStatements.finish,
      CallableIndexedOwnedAdmittedStagedTerminalBody.code, fallback] using
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code_rename result receipt.flow
        escaped (fallback result fellThrough) ξ))

private theorem tree_of_roots {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {policy : SourceCoreLoops.Policy} {view : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView invocation.source view)
    (roots : ∀ expression child, receipt.Children expression child →
      Nonempty (RootAt compiled context invocation scope expression child semanticFaults)) :
    ∃ rawResult, Nonempty (Tree compiled context invocation scope semanticFaults result rawResult
      statements flow) := by
  revert roots
  induction receipt with
  | terminal terminal generated =>
    intro roots
    obtain ⟨root⟩ := roots _ _ ⟨rfl, rfl⟩
    exact ⟨root.support.node.type, ⟨.terminal root
      (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head terminal metadata)
      terminal.sameType rfl⟩⟩
  | discard found form first generated tail accepted ih =>
    intro roots
    obtain ⟨root⟩ := roots _ _ (.inl ⟨rfl, rfl⟩)
    obtain ⟨rawResult, ⟨tailTree⟩⟩ := ih (fun expression child used =>
      roots expression child (.inr used))
    exact ⟨rawResult, ⟨.discard root (lookupStatement?_sound (metadata.statement found)) form tailTree⟩⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {capturedContext : Core.Context} {code : Code compiled.indexed function scope capturedContext}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  (packet : Sequence code stages)
  (support : SequenceSupport code inputs stages packet semanticFaults)
  {child : Staging.Recursive.Scope} (selected : stages.Closure function child)

include support selected in
/-- The original frame and literal parameter extension derive the declared raw
result for the tree assembled from the actual receipt and original Roots. -/
theorem issued_tree :
    Nonempty (Tree compiled inputs.context child (parameterScope code) semanticFaults
      code.receipt.resultCore function.resultType function.body packet.receipt.flow) := by
  have source : child.source = function.source := stages.source selected
  have metadata : LambdaMetadataViews.MetadataView child.source code.view := by
    simpa only [source] using code.viewOfSource
  obtain ⟨rawResult, ⟨tree⟩⟩ := tree_of_roots packet.receipt.tree metadata
    (fun expression childCode used => support.roots child selected expression childCode used)
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.frame inputs.extended
  rw [← source] at typed
  have unique : NodeOccurrencesUnique child.source := by
    rw [source]
    exact support.frame.code.graph.nodeOccurrencesUnique
  have sameRaw : rawResult = function.resultType :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport.raw_result
      unique tree typed completes
  subst rawResult
  exact ⟨tree⟩

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable {mapping : LocationMap} {world : StoreTyping}
  {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative (parameterScope code) environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before inputs.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : State headers keys ⟨parameterScope code, mapping, world, before, store, canonical⟩)
  (admitted : Admission
    (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
    inputs.context initial)

include support selected environments heaps locals agrees actualTyped admitted in
/-- The exact original body trace manufactures its flow outcome and literal
footer evaluation at the same reached parameter state. -/
theorem preserves_body {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget)
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size child inputs.context environment before function.body finalContext bodyOutcome after) :
    finalContext = inputs.context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧
      Staging.Recursive.BodyResult function.resultType bodyOutcome outcome ∧
      ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType code.receipt.resultCore callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  obtain ⟨tree⟩ := issued_tree packet support selected
  obtain ⟨sameContext, outcome, sameBody, value, finalStore, finalMap, finalWorld,
      flow, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds.preserves_flow
      (profile := profile) tree children environments heaps locals agrees actualTyped
      initial admitted within trace
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback code.receipt.resultCore packet.fellThrough).rename ξ)
      represented flow packet.escaped
  have evaluatedBody : Evaluates actual store (code.receipt.body.rename ξ) wholeValue finalStore := by
    rw [emitted_rename packet.receipt ξ]
    exact whole
  have bodyResult : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome := by
    rw [sameBody]
    exact CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _
  exact ⟨sameContext, outcome, sameBody, bodyResult, wholeValue, finalStore, finalMap, finalWorld,
    evaluatedBody, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include support selected environments heaps locals agrees actualTyped admitted in
/-- The literal footer exposes a strict native flow child. Its Source grade
and nested fault remain independent of the original completed native grade. -/
theorem reflects_body {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        child inputs.context environment before function.body inputs.context (control outcome) after ∧
      Staging.Recursive.BodyResult function.resultType (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType code.receipt.resultCore callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  obtain ⟨tree⟩ := issued_tree packet support selected
  have original := completed
  rw [emitted_rename packet.receipt ξ] at original
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original (Nat.le_refl size)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds.reflects_flow
      (profile := profile) tree children environments heaps locals agrees actualTyped
      initial admitted (Nat.le_trans (Nat.le_of_lt strict) within) flowTrace
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback code.receipt.resultCore packet.fellThrough).rename ξ)
      represented flowTrace.sound packet.escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound whole
  cases same
  subst stores
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaBodyBounds
/-! The chosen recursive sequence packet supplies the existing shape-independent body
ports at the genuine parameter entry. Original parameter admission and native
allocation typing are reused literally. Strong numeric Root induction supplies
the evaluated children; no whole-body meaning is a static packet field. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Sequence SequenceSupport parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Sequence code stages)
  (support : SequenceSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  obtain ⟨_sameContext, produced, sameBody, _derivedResult, value, bodyStore, finalMap, finalWorld,
      evaluated, result, heaps, maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds.preserves_body
      (profile := profile) (packet := packet) (support := support) (selected := selected)
      (environments := entry.entry.environments) (heaps := entry.entry.heaps)
      (locals := entry.entry.locals) (agrees := entry.entry.lookups)
      (actualTyped := entry.entry.actualTyped) (initial := reached) (admitted := admitted)
      children within trace
  have sameOutcome : outcome = produced :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, returned, related, post⟩

include support stable beforeTyped argumentsTyped in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, meaning,
      heaps, maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds.reflects_body
      (profile := profile) (packet := packet) (support := support) (selected := packet.selected)
      (environments := entry.environments) (heaps := entry.heaps)
      (locals := entry.locals) (agrees := entry.lookups) (actualTyped := entry.actualTyped)
      (initial := reached) (admitted := admitted) children within completed
  exact ⟨sourceSize, inputs.context, control outcome, outcome, after, finalMap, finalWorld,
    trace, matched, meaning, heaps, maps, worlds, frame, metadata, returned, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaApplicationBounds
/-! A chosen real recursive sequence body fills the existing closure application ports.
Parameter installation and the saved caller restoration remain their original
producers. The body ports are manufactured from static support and the strict
Root induction hypothesis, preserving the literal returned pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Sequence SequenceSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Sequence code stages)
  (support : SequenceSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- The genuine Source application chooses its own scope and parameter entry.
The same internally constructed body port returns through the saved caller. -/
theorem application_preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaBodyBounds.source_body_at
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached children (Nat.le_of_lt strict))
    trace within

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- Native application selects its real strict body child. The packet's
chosen Source scope supplies that body and the original returned caller post. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaBodyBounds.native_body_at
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid children (Nat.le_of_lt strict))
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
/-! The original retained production recipe constructs a recursive discard
sequence packet at the actual Code. The checked original-source issuer supplies
Roots for every recorded child at every genuinely selected scope. Ordinary and
principal Associations retain their own named seed, Code and BodyWith context.
Original policy, declarations, syntax and exact issued-call readiness remain
static inputs; the packet stores no execution or whole-body meaning law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaBodyRecipes (Retained BodyRecipe)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyOn)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditionsOn)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
  (Sequence SequenceSupport PacketFor SupportFor parameterScope)
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

/-- One chosen sequence retains the same exact compiler callback, reason and fuel. -/
structure Choice where
  packet : Sequence code stages
  callback : packet.policy.lowerExpression =
    FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  fuel : packet.fuel = code.fuel

/-- Actual compilation supplies the ordered receipt and finish footer.
The supported grammar and genuine Source-selected child remain static inputs. -/
theorem choose (named : Named) (retained : Retained named code)
    (shape : CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Shape
      code.view function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Choice code (stages := stages)) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) code policy callback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed named compilation.own.assignments diagnostics expression)
    shape accepted
  let packet : Sequence code stages := {
    policy := policy
    fuel := code.fuel
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    receipt := receipt
    child := child
    selected := selected }
  exact ⟨{
    packet := packet
    callback := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.expression_callback
      compiled.indexed named compilation.own.assignments diagnostics expression
    reason := rfl
    fuel := rfl }⟩

variable (body : CallableIndexedLambdaStaticBodySupport.BodyWith
  (values := .initial compiled.compatible.checked) expressionSyntax certificates code
  (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
  (choice : Choice code (stages := stages))

/-- Original policy and typing authority are independent of the retained recipe.
Each syntactic child and each issued-call proof belongs to this same receipt. -/
structure Conditions where
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure function child → LocalView child.source code.view changed
  avoids : ∀ child, stages.Closure function child →
    Avoids child.source (function.body.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure function child →
    PolicyOn code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source
      (parameterScope code) choice.packet.reasonAt
      (fun id => Reaches child.source (function.body.map NodeId.statement) (.expression id))
  viewProfile : PolicyOn code.policy code.compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) code.view
    (parameterScope code) choice.packet.reasonAt
    (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id))
  syntaxTree : ∀ expression childCode,
    choice.packet.receipt.tree.Children expression childCode → Syntax code.view expression
  original : ∀ child, stages.Closure function child →
    OriginalConditionsOn compiled code.policy code.compilation readFuel body.toContext.context child
      choice.packet.reasonAt (parameterScope code) (function.body.map NodeId.statement) semanticFaults

/-- The checked issuer transports actual reached actions to original Source.
Frame and parameter typing come from the same BodyWith input context. -/
theorem static (conditions : Conditions code body choice)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport.Static
      (statementPolicy := choice.packet.policy) (fuel := choice.packet.fuel)
      (view := code.view) (scope := parameterScope code) (statements := function.body)
      (result := code.receipt.resultCore) (reasonAt := choice.packet.reasonAt)
      (fellThrough := choice.packet.fellThrough) (escaped := choice.packet.escaped)
      (bodyCode := code.receipt.body) (compiled := compiled) (function := function)
      (context := body.toContext.context) (types := body.toContext.types)
      (invocation := child) (changed := conditions.changed)
      (policy := code.policy) (lowerBody := code.lowerBody) (compilation := code.compilation)
      (readFuel := conditions.readFuel) (bodyFuel := code.fuel) (semanticFaults := semanticFaults)
      (native := some compiled.indexed.ancestry.graph.inputs.callable) (active := code.active)
      choice.packet.receipt := {
  edited := conditions.edited child selected
  avoids := conditions.avoids child selected
  sourceProfile := conditions.sourceProfile child selected
  viewProfile := conditions.viewProfile
  callables := code.callables
  expressionCallback := by
    funext childFuel actualSource current expression reasonAt
    have callbackAt := congrArg
      (fun lower : SourceCoreFunctions.ExpressionLowerer =>
        lower childFuel actualSource current expression reasonAt) choice.callback
    simpa only [FunctionCode.children] using callbackAt
  frame := body.frame
  parameters := body.toContext.extended
  sameSource := stages.source selected
  body := rfl
  syntaxTree := conditions.syntaxTree
  conditions := conditions.original child selected }

/-- Readiness quantifies only the exact certificates issued from this packet. -/
def Ready (conditions : Conditions code body choice) : Prop :=
  ∀ child selected, CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport.Ready
    (static code body choice conditions child selected)

/-- Every Source-selected scope receives its actual recorded original Roots.
The declared raw result is derived above the static packet layer. -/
def support (conditions : Conditions code body choice)
    (ready : Ready code body choice conditions) :
    SequenceSupport code body.toContext stages choice.packet semanticFaults := {
  frame := body.frame
  roots := fun child selected expression childCode used =>
    (static code body choice conditions child selected).root
      (ready child selected) expression childCode used }

section Association
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)

/-- The actual Association branch fixes its own Code and named seed. -/
def ChoiceFor : Type :=
  match association with
  | .ordinary _ _ actualCode _ _ _ _ _ _ _ _ => Choice actualCode (stages := stages)
  | .principal _ _ actualCode _ _ _ _ _ _ _ _ => Choice actualCode (stages := stages)

/-- The recursive grammar is witnessed at that same branch's compiler view. -/
def ShapeFor : Prop :=
  match association with
  | .ordinary _ _ actualCode _ _ _ _ _ _ _ _ =>
      CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Shape actualCode.view function.body
  | .principal _ _ actualCode _ _ _ _ _ _ _ _ =>
      CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Shape actualCode.view function.body

/-- The ordinary and principal recipes both come from authentic provenance.
The exact chosen Site is retained through recapture, with no data selector. -/
theorem choose_for (shape : ShapeFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (ChoiceFor association (stages := stages)) := by
  cases association with
  | ordinary owner captured actualCode history actualSupport origin prefixContext globals referenceIndex typed provenance =>
      exact choose actualCode actualSupport.caller.named provenance.body_recipe shape child selected
  | principal owner captured actualCode history actualSupport origin globals leading referenceIndex typed provenance =>
      exact choose actualCode actualSupport.principal.named provenance.body_recipe shape child selected

/-- Static authority uses the branch's literal BodyWith parameter input context. -/
def ConditionsFor (chosen : ChoiceFor association (stages := stages)) : Type :=
  match association with
  | .ordinary _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Conditions actualCode actualSupport.body chosen
  | .principal _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Conditions actualCode actualSupport.body chosen

/-- Call authority stays indexed by each exact internally issued certificate. -/
def ReadyFor (chosen : ChoiceFor association (stages := stages))
    (conditions : ConditionsFor association chosen) : Prop :=
  match association with
  | .ordinary _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Ready actualCode actualSupport.body chosen conditions
  | .principal _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Ready actualCode actualSupport.body chosen conditions

/-- The same chosen sequence packet enters the existing mixed body sum. -/
def packet_for (chosen : ChoiceFor association (stages := stages)) : PacketFor association stages :=
  match association with
  | .ordinary _ _ _ _ _ _ _ _ _ _ _ => .sequence chosen.packet
  | .principal _ _ _ _ _ _ _ _ _ _ _ => .sequence chosen.packet

/-- Both branches retain their own Code and actual body.toContext.
This produces support for the explicit chosen packet; no global coverage is inferred. -/
def support_for (chosen : ChoiceFor association (stages := stages))
    (conditions : ConditionsFor association chosen) (ready : ReadyFor association chosen conditions) :
    SupportFor association stages (packet_for association chosen) := by
  cases association with
  | ordinary owner captured actualCode history actualSupport origin prefixContext globals referenceIndex typed provenance =>
      exact support actualCode actualSupport.body chosen conditions ready
  | principal owner captured actualCode history actualSupport origin globals leading referenceIndex typed provenance =>
      exact support actualCode actualSupport.body chosen conditions ready
end Association

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryDiscardSequenceReadiness
/-! Ordinary public preparation constructs call readiness for the exact child
certificates issued by one retained discard-sequence packet. Original static
authority, both policy profiles, view transport and the genuine source receipt
remain inputs. The registry is the actual Selected relation; this theorem does
not extend ordinary owner recovery to implementation-method histories. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryDiscardSequenceReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate)
open CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories (Choice Conditions)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : CallableIndexedNamedGeneration.Named}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

/-- Every genuine selected ordinary scope receives call ports for this same
issuer's finite certificate. Child typing comes from its original frame and
parameter receipt; the supplied static conditions contain no CallsReady law. -/
theorem ready_of_preparation
    (code : Code compiled.indexed function scope administrative)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
    (choice : Choice code (stages := RecursiveStageRegistry.registry compiled.sourceProgram
      compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table))
    (conditions : Conditions code body choice)
    (readFuel_eq : conditions.readFuel = compiled.indexed.fuel)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id) :
    CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories.Ready
      code body choice conditions := by
  intro invocation selected
  let packet := CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories.static
    code body choice conditions invocation selected
  refine ⟨?_⟩
  intro expression child used
  have typed := (packet.authority expression child used).typed
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.syntax_original
    packet.edited packet.avoids (packet.syntaxTree expression child used)
    (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
      choice.packet.receipt.tree packet.edited.metadata expression child used)
  have root : Certificate code.policy code.lowerBody code.compilation conditions.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source body.toContext.context choice.packet.reasonAt
      (CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.parameterScope code)
      expression child := packet.certificate expression child used
  have atIndices (readFuel : Nat) (reasonAt : ExpressionId → Word)
      (sameFuel : readFuel = compiled.indexed.fuel)
      (sameReason : reasonAt = code.reasonAt)
      (certificate : Certificate code.policy code.lowerBody code.compilation readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source body.toContext.context reasonAt
        (CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.parameterScope code)
        expression child) :
      CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
        (compiled := compiled) (invocation := invocation) certificate := by
    subst readFuel
    subst reasonAt
    exact CallableOrdinaryPreparedScopeAnnotationCallsReady.calls_ready
      code retained metadata sourceReceipt unique accepted wellFormed signatureMember sourceOwner
      selected typed certificate syntaxTree
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  exact atIndices conditions.readFuel choice.packet.reasonAt readFuel_eq choice.reason root compiler path

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryDiscardSequenceReadiness
end
