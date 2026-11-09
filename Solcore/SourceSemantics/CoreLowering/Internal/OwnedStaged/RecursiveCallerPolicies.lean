import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.Staging.RecursiveProfile
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.FiniteClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.FiniteCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection

/-!
# Staged bounds: recursive caller policies

Policy profiles and bounds of recursive callers, and the transport of recursive body views.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles
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
  | unary (operator : Solcore.Syntax.UnaryOp) (operand : ExpressionId) : SupportedForm (.unary operator operand)
  | binary (left : ExpressionId) (operator : Solcore.Syntax.BinaryOp) (right : ExpressionId) : SupportedForm (.binary left operator right)
  | conditional (condition yes no : ExpressionId) : SupportedForm (.conditional condition yes no)
  | group (inner : ExpressionId) : SupportedForm (.group inner)
  | tuple (ids : List ExpressionId) : SupportedForm (.tuple ids)
  | constructor (instantiation : DataConstructorInstantiation) (ids : List ExpressionId) :
      SupportedForm (.constructor instantiation ids)
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
  | constructor found form _ranges _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .constructor _ _
  | call found form _callee _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .call _ _ _

  | unary found form _child =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .unary _ _
  | binary found form _first _second =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .binary _ _ _
  | conditional found form _condition _then _else =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .conditional _ _ _

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

structure MetadataOn (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) (allowed : ExpressionId → Prop) : Prop where
  requirements : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → node.requirements = []
  coercions : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  localRead : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

/-- Native literals keep their genuine selected evidence rows. Their compiler
validator authenticates those rows; other admitted expressions retain empty
requirements. This is a metadata condition, not an execution premise. -/
structure NativeMetadataFor (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) : Prop where
  requirements : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution
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

structure NativeMetadataOn (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) (allowed : ExpressionId → Prop) : Prop where
  requirements : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution
  coercions : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  localRead : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

theorem NativeMetadataFor.of_ordinary (metadata : MetadataFor prepared named source) :
    NativeMetadataFor prepared named source :=
  ⟨fun id tree node found => .inl (metadata.requirements id tree node found),
    metadata.coercions, metadata.initializer, metadata.arguments, metadata.localRead⟩

theorem NativeMetadataOn.of_ordinary {allowed : ExpressionId → Prop}
    (metadata : MetadataOn prepared named source allowed) : NativeMetadataOn prepared named source allowed :=
  ⟨fun id reached tree node found => .inl (metadata.requirements id reached tree node found),
    metadata.coercions, metadata.initializer, metadata.arguments, metadata.localRead⟩

theorem NativeMetadataFor.on (metadata : NativeMetadataFor prepared named source)
    (allowed : ExpressionId → Prop) : NativeMetadataOn prepared named source allowed :=
  ⟨fun id _ tree => metadata.requirements id tree,
   fun id _ tree => metadata.coercions id tree,
   fun id _ tree => metadata.initializer id tree,
   fun id _ tree => metadata.arguments id tree,
   fun id _ tree => metadata.localRead id tree⟩

theorem MetadataFor.on (metadata : MetadataFor prepared named source)
    (allowed : ExpressionId → Prop) : MetadataOn prepared named source allowed :=
  ⟨fun id _ tree => metadata.requirements id tree,
   fun id _ tree => metadata.coercions id tree,
   fun id _ tree => metadata.initializer id tree,
   fun id _ tree => metadata.arguments id tree,
   fun id _ tree => metadata.localRead id tree⟩

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
  | unary | binary | conditional | group | constructor => simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  | tuple => simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  | call => simp [SourceCoreGeneralFunctions.contextualSource, found, form]

private theorem evidence_none
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (current : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) {id : ExpressionId} {node : ExpressionNode}
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    (found : source.lookupExpression? id = some node) (supported : SupportedForm node.form)
    (requirements : node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution) (coercions : node.coercions = [])
    (arguments : ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller current child budget
      source scope id reasonAt callables = .ok none := by
  rcases requirements with requirements | ⟨literal, resolution, form⟩
  ·
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
    | unary | binary | conditional | group | constructor =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
    | tuple =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
    | call callee ids metadata =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
        arguments callee ids metadata form]
  · have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some node.requirements := by
      unfold SourceCompilationPlan.ordinaryOwnedRequirements?
      rw [coercions]
      change (if node.requirements.length < 0 then none else
        if node.requirements = node.requirements.take (node.requirements.length - 0) ++ [] then
          some (node.requirements.take (node.requirements.length - 0)) else none) = some node.requirements
      simp
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, coercions]

private theorem special_none
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    (metadata : NativeMetadataFor prepared named source)
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
  | unary | binary | conditional | group | constructor => rfl
  | tuple => rfl
  | call => rfl

theorem recipe_policy_for_native
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : NativeMetadataFor prepared named source)
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


theorem recipe_policy_for
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy (context prepared named)
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt := by
  exact recipe_policy_for_native recipe (NativeMetadataFor.of_ordinary metadata) scope reasonAt

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

theorem retained_policy_for_native
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : NativeMetadataFor prepared named source)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact recipe_policy_for_native recipe metadata scope reasonAt


private theorem special_none_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    {allowed : ExpressionId → Prop}
    (metadata : NativeMetadataOn prepared named source allowed)
    {id : ExpressionId}
    (admitted : allowed id)
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id admitted tree node found)
  have noEvidence := evidence_none prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized (context prepared named) child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found supported
    (metadata.requirements id admitted tree node found) (metadata.coercions id admitted tree node found)
    (metadata.arguments id admitted tree node found)
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id admitted tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id admitted tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | unary | binary | conditional | group | constructor => rfl
  | tuple => rfl
  | call => rfl

theorem recipe_policy_on_native
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {allowed : ExpressionId → Prop}
    (metadata : NativeMetadataOn prepared named source allowed)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn policy (context prepared named)
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt allowed := by
  constructor
  · intro id admitted tree child budget
    rw [recipe.lowerSpecial]
    exact special_none_on compilation rootFuel metadata admitted tree child budget scope reasonAt
  · intro id admitted tree
    obtain ⟨node, found, supported⟩ := syntax_node tree
    have sameSource := contextual_same found supported (metadata.localRead id admitted tree node found)
    rw [recipe.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  · exact recipe.lowerRead
  · exact recipe.leafLowerer


theorem recipe_policy_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {allowed : ExpressionId → Prop}
    (metadata : MetadataOn prepared named source allowed)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn policy (context prepared named)
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt allowed := by
  exact recipe_policy_on_native recipe (NativeMetadataOn.of_ordinary metadata) scope reasonAt

/-- The full profile is proved from one actual retained production recipe.
The independent raw typing, scope declarations and CallsReady remain separate. -/
theorem retained_policy_on
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    {allowed : ExpressionId → Prop}
    (metadata : MetadataOn prepared named source allowed)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt allowed := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact recipe_policy_on recipe metadata scope reasonAt


theorem retained_policy_on_native
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    {allowed : ExpressionId → Prop}
    (metadata : NativeMetadataOn prepared named source allowed)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt allowed := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact recipe_policy_on_native recipe metadata scope reasonAt



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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport
/-! Static steps for original-source recursive compiler-action transport.
  Actual reached lookups preserve complete nodes. Metadata preserves declared
  binders, and the production indirect-call hook ignores its Source argument.
  Full compiler-action equality follows its actual fuel recursion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)

section Syntax
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
include edited avoids

/-- Recursive syntax crosses only actual reached, unedited occurrences. -/
theorem syntax_view {id : ExpressionId} (tree : Syntax source id)
    (reached : Reaches source roots (.expression id)) : Syntax view id := by
  revert reached
  induction tree with
  | leaf finite =>
      intro reached
      exact .leaf (CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport.finite_syntax
        edited avoids finite reached)
  | @group id node inner found form child ih =>
      intro reached
      have innerReached : Reaches source roots (.expression inner) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .group ((expression_lookup edited avoids reached).symm.trans found) form (ih innerReached)
  | @tuple id node ids found form children ih =>
      intro reached
      exact .tuple ((expression_lookup edited avoids reached).symm.trans found) form
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @constructor id node instantiation ids found form ranges children ih =>
      intro reached
      exact .constructor ((expression_lookup edited avoids reached).symm.trans found) form ranges
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @call id node callee ids metadata found form calleeTree children calleeIH childrenIH =>
      intro reached
      have calleeReached : Reaches source roots (.expression callee) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .call ((expression_lookup edited avoids reached).symm.trans found) form
        (calleeIH calleeReached)
        (fun child member => childrenIH child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @unary id node operator operand found form child ih =>
      intro reached
      exact .unary ((expression_lookup edited avoids reached).symm.trans found) form
        (ih (.expression reached found (by simp [form, ExpressionForm.references])))
  | @binary id node left operator right found form first second firstIH secondIH =>
      intro reached
      exact .binary ((expression_lookup edited avoids reached).symm.trans found) form
        (firstIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (secondIH (.expression reached found (by simp [form, ExpressionForm.references])))
  | @conditional id node condition yes no found form test thenBranch elseBranch testIH thenIH elseIH =>
      intro reached
      exact .conditional ((expression_lookup edited avoids reached).symm.trans found) form
        (testIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (thenIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (elseIH (.expression reached found (by simp [form, ExpressionForm.references])))

/-- Reverse syntax uses the original body's authentic reachability path. -/
theorem syntax_original {id : ExpressionId} (tree : Syntax view id)
    (reached : Reaches source roots (.expression id)) : Syntax source id := by
  have reverse : LocalView view source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  exact syntax_view reverse (avoids.view edited.metadata) tree (reached.metadata edited.metadata)
end Syntax

/-- Compatible read policy retains requirements, coercions and projected type
  because its actual full node lookup and owner stay equal. -/
theorem compatible_read_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId}
    (lookup : source.lookupExpression? id = view.lookupExpression? id) :
    SourceCoreCompatibleDataExpressions.readExpression checked source id =
      SourceCoreCompatibleDataExpressions.readExpression checked view id := by
  simp only [SourceCoreCompatibleDataExpressions.readExpression, metadata.owner, lookup]

/-- The declared binder and exact lazy mapping encoder survive the same view;
  this follows from rootBinder transport rather than a raw type cast. -/
theorem compatible_lower_read_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word}
    (lookup : source.lookupExpression? id = view.lookupExpression? id) :
    SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id reason =
      SourceCoreCompatibleDataExpressions.lowerRead fuel values view scope id reason := by
  simp only [SourceCoreCompatibleDataExpressions.lowerRead,
    compatible_read_eq metadata lookup, metadata.owner, rootBinder metadata]

private theorem mapM_eq_of_members {α β ε : Type} {items : List α}
    {left right : α → Except ε β} (same : ∀ item, item ∈ items → left item = right item) :
    items.mapM left = items.mapM right := by
  revert same
  induction items with
  | nil => intro _same; rfl
  | cons item rest ih =>
      intro same
      simp only [List.mapM_cons]
      rw [same item (by simp), ih (fun next member => same next (by simp [member]))]

/-- The validator reads the literal callee plus the ordered arguments. Full
  lookup equality preserves every type, raw type and coercion check. -/
theorem indirect_validator_eq {source view : TypedSource}
    {node : ExpressionNode} {callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution}
    (calleeLookup : source.lookupExpression? callee = view.lookupExpression? callee)
    (argumentLookups : ∀ child, child ∈ ids →
      source.lookupExpression? child = view.lookupExpression? child) :
    SourceCompilationPlan.validateIndirectCallMetadata source node callee ids metadata =
      SourceCompilationPlan.validateIndirectCallMetadata view node callee ids metadata := by
  have calleeExact : SourceCompilationPlan.exactExpression source callee =
      SourceCompilationPlan.exactExpression view callee := by
    simp only [SourceCompilationPlan.exactExpression, calleeLookup]
  have argumentTypes : ids.mapM (fun child => do
      let actual ← SourceCompilationPlan.exactExpression source child
      pure actual.type) = ids.mapM (fun child => do
      let actual ← SourceCompilationPlan.exactExpression view child
      pure actual.type) := by
    apply mapM_eq_of_members
    intro child member
    simp only [SourceCompilationPlan.exactExpression, argumentLookups child member]
  simp only [SourceCompilationPlan.validateIndirectCallMetadata, calleeExact, argumentTypes]

/-- Both production policy branches ignore the Source argument of callCallable.
  The actual node, compilation context, table and diagnostic owner are fixed. -/
theorem production_call_eq (native : Option SourceCoreGeneralFunctions.CallableContext)
    (active : TypeSystem.Substitution) (compilation : SourceCoreFunctions.Context)
    (source view : TypedSource) (node : ExpressionNode) (result : Ty)
    (callee arguments : Expr) :
    (SourceCoreGeneralFunctions.callablePolicy native active).callCallable
      compilation source node result callee arguments =
    (SourceCoreGeneralFunctions.callablePolicy native active).callCallable
      compilation view node result callee arguments := by
  cases native <;> rfl


private inductive FormInFragment : ExpressionForm → Prop where
  | atomic {form} (leaf : CompatibleExpressionLiterals.Atomic form) : FormInFragment form
  | read {name binder} : FormInFragment (.reference name (.local binder))
  | group {inner} : FormInFragment (.group inner)
  | tuple {ids} : FormInFragment (.tuple ids)
  | constructor {instantiation ids} : FormInFragment (.constructor instantiation ids)
  | call {callee ids metadata} : FormInFragment (.call callee ids (.indirect metadata))
  | unary {operator operand} : FormInFragment (.unary operator operand)
  | binary {left operator right} : FormInFragment (.binary left operator right)
  | conditional {test yes no} : FormInFragment (.conditional test yes no)

private theorem syntax_found {source : TypedSource} {id : ExpressionId}
    (tree : Syntax source id) : ∃ node, source.lookupExpression? id = some node := by
  cases tree with
  | leaf finite => cases finite <;> exact ⟨_, ‹source.lookupExpression? id = some _›⟩
  | group found _ _ => exact ⟨_, found⟩
  | tuple found _ _ => exact ⟨_, found⟩
  | constructor found _ _ _ => exact ⟨_, found⟩
  | call found _ _ _ => exact ⟨_, found⟩
  | unary found _ _ => exact ⟨_, found⟩
  | binary found _ _ _ => exact ⟨_, found⟩
  | conditional found _ _ _ _ => exact ⟨_, found⟩

private theorem syntax_form {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (tree : Syntax source id) (found : source.lookupExpression? id = some node) :
    FormInFragment node.form := by
  cases tree with
  | leaf finite =>
      cases finite with
      | literal selected atomic =>
          cases Option.some.inj (selected.symm.trans found)
          exact .atomic atomic
      | read selected form =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.read
      | group selected form _ =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.group
      | pair selected form _ _ =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.tuple
  | group selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.group
  | tuple selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.tuple
  | constructor selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.constructor
  | call selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.call
  | unary selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.unary
  | binary selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.binary
  | conditional selected form _ _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.conditional

/-- Direct references obtain their syntax from the actual finite parent tree.
The projection preserves the literal argument vector, including duplicates. -/
private theorem syntax_child {source : TypedSource} {id child : ExpressionId}
    {node : ExpressionNode} (tree : Syntax source id)
    (found : source.lookupExpression? id = some node)
    (edge : (.expression child : NodeId) ∈ node.form.references) : Syntax source child := by
  cases tree with
  | leaf finite =>
      cases finite with
      | literal selected atomic =>
          cases Option.some.inj (selected.symm.trans found)
          generalize formEq : node.form = actualForm at atomic
          cases atomic <;> simp [formEq, ExpressionForm.references] at edge
      | read selected form =>
          cases Option.some.inj (selected.symm.trans found)
          simp [form, ExpressionForm.references] at edge
      | @group _ _ inner selected form innerTree =>
          cases Option.some.inj (selected.symm.trans found)
          have same : child = inner := by simpa [form, ExpressionForm.references] using edge
          exact same.symm ▸ Syntax.leaf innerTree
      | @pair _ _ left right selected form first second =>
          cases Option.some.inj (selected.symm.trans found)
          have member : child = left ∨ child = right := by
            simpa [form, ExpressionForm.references] using edge
          rcases member with same | same
          · exact same.symm ▸ Syntax.leaf first
          · exact same.symm ▸ Syntax.leaf second
  | @group _ _ inner selected form innerTree =>
      cases Option.some.inj (selected.symm.trans found)
      have same : child = inner := by simpa [form, ExpressionForm.references] using edge
      exact same.symm ▸ innerTree
  | tuple selected form children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, ExpressionForm.references] using edge)
  | constructor selected form _ranges children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, ExpressionForm.references] using edge)
  | @call _ _ callee ids _ selected form calleeTree children =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = callee ∨ child ∈ ids := by
        simpa [form, ExpressionForm.references] using edge
      rcases member with same | member
      · exact same.symm ▸ calleeTree
      · exact children child member
  | @unary _ _ operator operand selected form childTree =>
      cases Option.some.inj (selected.symm.trans found)
      have same : child = operand := by simpa [form, ExpressionForm.references] using edge
      exact same.symm ▸ childTree
  | @binary _ _ left operator right selected form first second =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = left ∨ child = right := by simpa [form, ExpressionForm.references] using edge
      rcases member with same | same
      · exact same.symm ▸ first
      · exact same.symm ▸ second
  | @conditional _ _ test yes no selected form testTree yesTree noTree =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = test ∨ child = yes ∨ child = no := by simpa [form, ExpressionForm.references] using edge
      rcases member with same | same | same
      · exact same.symm ▸ testTree
      · exact same.symm ▸ yesTree
      · exact same.symm ▸ noTree

private theorem basic_atomic_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (lookup : source.lookupExpression? id = view.lookupExpression? id)
    (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (reason : Word) :
    SourceCoreBasic.lowerExpression fuel source scope id reason =
      SourceCoreBasic.lowerExpression fuel view scope id reason := by
  have sameRead : SourceCoreBasic.readExpression source id = SourceCoreBasic.readExpression view id := by
    simp only [SourceCoreBasic.readExpression, metadata.owner, lookup]
  cases fuel with
  | zero => rfl
  | succ fuel =>
      conv => lhs; rw [SourceCoreBasic.lowerExpression]
      conv => rhs; rw [SourceCoreBasic.lowerExpression]
      cases reading : SourceCoreBasic.readExpression source id with
      | error error =>
          have viewReading := sameRead.symm.trans reading
          simp only [viewReading, bind, Except.bind]
      | ok output =>
          rcases output with ⟨actualNode, type⟩
          have readFound := (BasicExpressions.readExpression_certificate reading).1
          cases Option.some.inj (readFound.symm.trans found)
          have viewReading := sameRead.symm.trans reading
          generalize formEq : node.form = actualForm at atomic
          cases atomic <;>
            simp only [viewReading, formEq, bind, Except.bind, pure, Except.pure]

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn
    policy compilation readFuel values source scope reasonAt
      (fun id => Reaches source roots (.expression id)))
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn
    policy compilation readFuel values view scope reasonAt
      (fun id => Reaches view roots (.expression id)))
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
include edited avoids sourceProfile viewProfile

private theorem policy_read_eq {id : ExpressionId} (tree : Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    policy.readExpression source id = policy.readExpression view id := by
  rw [sourceProfile.read id reached tree,
    viewProfile.read id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)]
  exact compatible_read_eq edited.metadata (expression_lookup edited avoids reached)

include callables in
private theorem compiler_step_eq (fuel : Nat) {id : ExpressionId} {node : ExpressionNode}
    (tree : Syntax source id) (reached : Reaches source roots (.expression id))
    (found : source.lookupExpression? id = some node)
    (children : ∀ child, (.expression child : NodeId) ∈ node.form.references →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt =
        SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation view scope id reasonAt := by
  have lookup := expression_lookup edited avoids reached
  have viewFound := lookup.symm.trans found
  have sameRead := policy_read_eq edited avoids sourceProfile viewProfile tree reached
  have sourceBypass := sourceProfile.special id reached tree
    (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
  have viewBypass := viewProfile.special id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)
    (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
  by_cases owner : id.occurrence.owner = source.owner
  · have viewOwner := owner.trans edited.metadata.owner
    conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    have sourceOwned : ¬id.occurrence.owner ≠ source.owner := fun different => different owner
    have viewOwned : ¬id.occurrence.owner ≠ view.owner := fun different => different viewOwner
    simp only [if_neg sourceOwned, if_neg viewOwned,
      found, viewFound, bind, Except.bind, pure, Except.pure]
    cases hook : policy.lowerSpecial? <;> simp only [hook] at sourceBypass viewBypass ⊢
    all_goals try rw [sourceBypass, viewBypass]
    all_goals
      try dsimp only [bind, Except.bind, pure, Except.pure]
      cases reading : policy.readExpression source id with
      | error error =>
          have viewReading := sameRead.symm.trans reading
          cases form : node.form <;> try rfl
          all_goals simp only [viewReading]
      | ok output =>
          rcases output with ⟨actualNode, type⟩
          have compatibleReading := (sourceProfile.read id reached tree).symm.trans reading
          have actualMetadata := CompatibleExpressionReads.metadata_of_read compatibleReading
          cases Option.some.inj (actualMetadata.found.symm.trans found)
          have viewReading := sameRead.symm.trans reading
          have viewCompatibleReading :=
            (viewProfile.read id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)).symm.trans viewReading
          have clipped : min (fuel + 1) fuel = fuel := Nat.min_eq_right (Nat.le_succ fuel)
          have readLower := compatible_lower_read_eq edited.metadata (fuel := readFuel)
            (values := values) (scope := scope) (reason := reasonAt id) lookup
          have hookSame : ∀ result callee arguments,
              policy.callables.callCallable compilation source node result callee arguments =
                policy.callables.callCallable compilation view node result callee arguments := by
            intro result callee arguments
            rw [callables]
            exact production_call_eq native active compilation source view node result callee arguments
          have tupleChildren {ids : List ExpressionId} (form : node.form = .tuple ids) :
              ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                compilation source scope child reasonAt) =
              ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                compilation view scope child reasonAt) := by
            apply mapM_eq_of_members
            intro child member
            exact children child (by simp [form, ExpressionForm.references, member])
          have tupleLeaf {ids : List ExpressionId} (form : node.form = .tuple ids) :
              policy.leafLowerer
                  (fun budget childSource childScope childId childReasonAt =>
                    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                      compilation childSource childScope childId childReasonAt)
                  (fuel + 1) source scope id reasonAt =
              policy.leafLowerer
                  (fun budget childSource childScope childId childReasonAt =>
                    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                      compilation childSource childScope childId childReasonAt)
                  (fuel + 1) view scope id reasonAt := by
            rw [sourceProfile.leaf]
            simp only [SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading,
              viewCompatibleReading, bind, Except.bind, pure, Except.pure, form, clipped,
              tupleChildren form]
          have fragment := syntax_form tree found
          generalize formEq : node.form = actualForm at fragment
          cases fragment with
          | atomic atomic =>
              have atomicBasic := basic_atomic_eq edited.metadata found lookup (formEq.symm ▸ atomic)
                (fuel + 1) scope (reasonAt id)
              generalize atomicForm : actualForm = leafForm at atomic
              cases atomic with
              | unit =>
                  simp only [formEq, atomicForm, viewReading]
                  exact tupleLeaf (formEq.trans atomicForm)
              | bool name value =>
                  simp only [formEq, atomicForm, viewReading, sourceProfile.leaf,
                    SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading, viewCompatibleReading, bind, Except.bind, atomicBasic]
              | word literal =>
                  simp only [formEq, atomicForm, viewReading, sourceProfile.leaf,
                    SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading, viewCompatibleReading, bind, Except.bind, atomicBasic]
              | integer literal resolution => rfl
          | read =>
              simp only [formEq, viewReading, sourceProfile.lower, readLower]
          | @group inner =>
              have child := children inner (by simp [formEq, ExpressionForm.references])
              simp only [formEq, viewReading, child]
          | @tuple ids =>
              cases ids with
              | nil =>
                  simp only [formEq, viewReading, tupleLeaf formEq]
              | cons first rest =>
                  cases rest with
                  | nil =>
                      simp only [formEq, viewReading, tupleLeaf formEq]
                  | cons second tail =>
                      cases tail with
                      | nil =>
                          have firstSame := children first (by simp [formEq, ExpressionForm.references])
                          have secondSame := children second (by simp [formEq, ExpressionForm.references])
                          simp only [formEq, viewReading, firstSame, secondSame]
                      | cons third tail =>
                          simp only [formEq, viewReading, tupleLeaf formEq]
          | @constructor instantiation ids =>
              have argumentsSame : (ids.zip instantiation.payloadTypes).mapM (fun (argument, expected) => do
                  let expected ← SourceCoreCompatibleDataExpressions.projectType values.checked
                    (.occurrence id.occurrence) expected
                  let argument ← SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                    compilation source scope argument reasonAt
                  SourceCoreBasic.ensureType (.occurrence id.occurrence) expected argument.type
                  pure argument) =
                (ids.zip instantiation.payloadTypes).mapM (fun (argument, expected) => do
                  let expected ← SourceCoreCompatibleDataExpressions.projectType values.checked
                    (.occurrence id.occurrence) expected
                  let argument ← SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                    compilation view scope argument reasonAt
                  SourceCoreBasic.ensureType (.occurrence id.occurrence) expected argument.type
                  pure argument) := by
                apply mapM_eq_of_members
                intro pair member
                have child := children pair.1 (by
                  simp only [formEq, ExpressionForm.references, List.mem_map, NodeId.expression.injEq]
                  exact ⟨pair.1, (List.of_mem_zip member).1, rfl⟩)
                cases pair
                dsimp only at child ⊢
                rw [child]
              simp only [bind, Except.bind] at argumentsSame
              simp only [formEq, viewReading, sourceProfile.leaf,
                SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading,
                viewCompatibleReading, bind, Except.bind]
              simp only [SourceCoreCompatibleDataExpressions.lowerWithReasons, compatibleReading,
                viewCompatibleReading, bind, Except.bind, formEq, Nat.min_self, argumentsSame]
          | @unary operator operand =>
              have child := children operand (by simp [formEq, ExpressionForm.references])
              simp only [formEq, viewReading, child]
          | @binary left operator right =>
              have first := children left (by simp [formEq, ExpressionForm.references])
              have second := children right (by simp [formEq, ExpressionForm.references])
              simp only [formEq, viewReading, first, second]
          | @conditional condition yes no =>
              have test := children condition (by simp [formEq, ExpressionForm.references])
              have thenBranch := children yes (by simp [formEq, ExpressionForm.references])
              have elseBranch := children no (by simp [formEq, ExpressionForm.references])
              simp only [formEq, viewReading, test, thenBranch, elseBranch]
          | @call callee ids metadata =>
              have calleeReached : Reaches source roots (.expression callee) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have argumentReached : ∀ child, child ∈ ids → Reaches source roots (.expression child) :=
                fun child member => .expression reached found
                  (by simp [formEq, ExpressionForm.references, member])
              have validatorSame := indirect_validator_eq (node := node) (metadata := metadata)
                (expression_lookup edited avoids calleeReached)
                (fun child member => expression_lookup edited avoids (argumentReached child member))
              have calleeRead := policy_read_eq edited avoids sourceProfile viewProfile
                (syntax_child tree found (by simp [formEq, ExpressionForm.references])) calleeReached
              have calleeSame := children callee (by simp [formEq, ExpressionForm.references])
              have argumentsSame : ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
                ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) := by
                apply mapM_eq_of_members
                intro child member
                exact children child (by simp [formEq, ExpressionForm.references, member])
              simp only [formEq, viewReading, validatorSame, calleeRead, calleeSame, argumentsSame, hookSame]
  · have viewOwner : id.occurrence.owner ≠ view.owner :=
      fun same => owner (same.trans edited.metadata.owner.symm)
    conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    simp only [if_pos owner, if_pos viewOwner]
    change Except.error (.ownerMismatch source.owner id.occurrence.owner) =
      (Except.error (.ownerMismatch view.owner id.occurrence.owner) :
        Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr)
    rw [edited.metadata.owner]

include callables in
/-- The actual production compiler returns the same complete action on every
reached node of the supported recursive grammar. Compiler fuel is identical;
child equalities follow its real predecessor recursion, including ordered
vectors. No evaluator, raw-type cast, or arbitrary source-insensitive policy is
assumed. -/
theorem compiler_eq_on (fuel : Nat) {id : ExpressionId} (tree : Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope id reasonAt := by
  induction fuel generalizing id with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy]
  | succ fuel ih =>
      obtain ⟨node, found⟩ := syntax_found tree
      apply compiler_step_eq edited avoids sourceProfile viewProfile callables fuel tree reached found
      intro child edge
      exact ih (syntax_child tree found edge) (.expression reached found edge)

include callables in
/-- An accepted Code.view action transfers to the original Source through the
same factory action, after its actual recursive syntax has been transported.
Raw typing and declaration authority remain original-source issuer inputs. -/
theorem accepted_original_on (fuel : Nat) {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Syntax view id) (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation view scope id reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation source scope id reasonAt = .ok lowered := by
  exact (compiler_eq_on edited avoids sourceProfile viewProfile callables fuel
    (syntax_original edited avoids tree reached) reached).trans accepted
end Compiler

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor
    policy compilation readFuel values source scope reasonAt)
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor
    policy compilation readFuel values view scope reasonAt)
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
include edited avoids sourceProfile viewProfile callables

/-- Existing global policy callers restrict their facts to the actual body. -/
theorem compiler_eq (fuel : Nat) {id : ExpressionId} (tree : Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope id reasonAt :=
  compiler_eq_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables fuel tree reached

/-- Compatibility wrapper for complete global profiles. -/
theorem accepted_original (fuel : Nat) {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Syntax view id) (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation view scope id reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation source scope id reasonAt = .ok lowered :=
  accepted_original_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables fuel tree reached accepted
end Compiler

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerBounds
/-! Structural recursion over the actual finite caller certificate constructs
all child expression meanings internally. Unary, binary and conditional roots
retain their recursive child certificates and reachable call authority. Grouping reflects at the same native
grade, and singleton tuples use the inclusive native child budget. Calls retain
the exact compiler entry vector and consume only static authority for calls
reachable in this root. Independent Source grades, fault scopes and reached
caller posts are retained. No child or called-body execution law is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds (FiniteFor)
open CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls NoMethods NoDirect NoIndexes)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {readFuel : Nat}

/-- Authority is required only for actual calls inside this exact root. Each
Port carries original prepared compiler metadata, with no execution field. -/
def CallsReady {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) : Prop :=
  ∀ {callFuel callScope callId actualCallee actualIds actualMetadata actualCode}
    (compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation
      invocation.source callScope callId actualCallee actualIds actualMetadata reasonAt actualCode),
    Calls compiler root → Nonempty
      (CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds.Port
        (compiled := compiled) (invocation := invocation) compiler)

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    Nonempty (FiniteFor (registry := completion.result.context.registry) (stages := stages) association))
  (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
  (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
    stages.Closure header.function child → child.evidence.Covers header.context)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
  sameLedger runtimeLedger uninitialized in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. No semantic continuation appears in the public inputs. -/
theorem preserves [FunctionCalls.FaultTokens semanticFaults] {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    NoMethods root → NoDirect root → NoIndexes root → CallsReady root → ∀ size,
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  induction root with
  | proxy receipt =>
      intro _noMethods _noDirect _noIndexes _ports size current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedAdmittedStagedProxyBounds.preserves
        functions extension bridge unique callFaults size (.proxy receipt)
  | leaf tree =>
      intro _noMethods _noDirect _noIndexes _ports size current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves
        bridge functions extension sameLedger runtimeLedger callFaults uninitialized semantic
        unique wellFormed runtime covers size tree
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih (fun compiler inside => noMethods compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => noDirect compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => ports compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst (fun compiler inside => noMethods compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => noDirect compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => ports compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond (fun compiler inside => noMethods compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => noDirect compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => ports compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihCondition (fun compiler inside => noMethods compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen (fun compiler inside => noMethods compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse (fun compiler inside => noMethods compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro childSize _smaller current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih (fun compiler inside => noMethods compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => noDirect compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => ports compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size
        childMeaning size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun compiler inside => noMethods compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => noDirect compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => ports compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_preserves
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun compiler inside => noMethods compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun compiler inside => noDirect compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun compiler inside => ports compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_preserves
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun nested inside => noMethods nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => noDirect nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => ports nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds.preserves
        bridge functions observations callFaults unique wellFormed runtime covers
        (compiler.result ▸ compiler.metadata) compiler.form nativeTypes size sequence childMeaning
        ⟨rfl, rfl, compiler.output⟩
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree _ihFirst _ihSecond =>
      intro _noMethods _noDirect noIndexes
      exact False.elim (noIndexes header keyFound form sourceType (.here firstTree secondTree))
  | @method id fuel lowered types compiler sequence children _ih =>
      intro  noMethods
      exact False.elim (noMethods compiler (.here sequence children))
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children _ih =>
      intro noMethods noDirect
      exact False.elim (noDirect compiler (.here calleeTyped application sequence children))
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun nested inside => noMethods nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => noDirect nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => ports nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := ports compiler (.here sequence children)
      have calleeCertified : RecursiveStageTupleMeaning.Entries rootScope compiler.entries
          rootScope callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds.preserves
        bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
        actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
        compiler port calleeCertified sequence size childMeaning ⟨rfl, rfl, rfl⟩

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
  sameLedger runtimeLedger uninitialized in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects [FunctionCalls.FaultTokens semanticFaults] (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    NoMethods root → NoDirect root → NoIndexes root → CallsReady root → ∀ size,
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  induction root with
  | proxy receipt =>
      intro _noMethods _noDirect _noIndexes _ports size current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedAdmittedStagedProxyBounds.reflects
        functions extension bridge callFaults size (.proxy receipt)
  | leaf tree =>
      intro _noMethods _noDirect _noIndexes _ports size current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects
        bridge functions extension sameLedger runtimeLedger callFaults uninitialized semantic
        unique wellFormed runtime covers size tree
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih (fun compiler inside => noMethods compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => noDirect compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => ports compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst (fun compiler inside => noMethods compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => noDirect compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => ports compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond (fun compiler inside => noMethods compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => noDirect compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => ports compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihCondition (fun compiler inside => noMethods compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen (fun compiler inside => noMethods compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse (fun compiler inside => noMethods compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : ReflectsAt bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih (fun compiler inside => noMethods compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => noDirect compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => ports compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) size ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size
        childMeaning (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults (size + 1) := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun compiler inside => noMethods compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => noDirect compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => ports compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_reflects
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun compiler inside => noMethods compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun compiler inside => noDirect compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun compiler inside => ports compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_reflects
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun nested inside => noMethods nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => noDirect nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => ports nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds.reflects
        bridge functions observations callFaults unique wellFormed runtime covers
        (compiler.result ▸ compiler.metadata) compiler.form nativeTypes size sequence childMeaning
        ⟨rfl, rfl, compiler.output⟩
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree _ihFirst _ihSecond =>
      intro _noMethods _noDirect noIndexes
      exact False.elim (noIndexes header keyFound form sourceType (.here firstTree secondTree))
  | @method id fuel lowered types compiler sequence children _ih =>
      intro  noMethods
      exact False.elim (noMethods compiler (.here sequence children))
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children _ih =>
      intro noMethods noDirect
      exact False.elim (noDirect compiler (.here calleeTyped application sequence children))
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro noMethods noDirect noIndexes ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun nested inside => noMethods nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => noDirect nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => ports nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := ports compiler (.here sequence children)
      have calleeCertified : RecursiveStageTupleMeaning.Entries rootScope compiler.entries
          rootScope callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds.reflects
        bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
        actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
        stageEq compiler port calleeCertified sequence size childMeaning ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCompilerBounds
/-! Successful compilation supplies the finite caller certificate internally.
These public entry ports compose the actual raw typing/compiler issuer with
the structural semantic fold. Static call authority is indexed by that exact
issued proof; no child or body execution law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCompilerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds (FiniteFor)
open CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

open CallableIndexedOwnedPreparedStagedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {reasonAt : ExpressionId → Word}

variable {readFuel : Nat}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    Nonempty (FiniteFor (registry := completion.result.context.registry) (stages := stages) association))
  (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
  (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
    stages.Closure header.function child → child.evidence.Covers header.context)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
  sameLedger runtimeLedger uninitialized in
/-- The accepted compiler action issues the actual tree used for Source preservation. -/
theorem preserves_compiled [FunctionCalls.FaultTokens semanticFaults]
    {rootScope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source rootScope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy
      compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source rootScope reasonAt)
    (coercions : ∀ id node,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [])
    {rootId : ExpressionId}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
    (typed : ExpressionHasType invocation.source context rootId node.type)
    {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation
      invocation.source rootScope rootId reasonAt = .ok rootCode)
    (ports : CallsReady (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted))
    (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
    let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted
    intro scope id lowered certified
    exact CallableIndexedOwnedPreparedStagedRecursiveCallerBounds.preserves
      bridge receiver stagePrepared profile wellFormed runtime covers unique
      actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
      sameLedger runtimeLedger uninitialized root (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy root syntaxTree policyFor)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root syntaxTree)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root syntaxTree) ports size certified

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
  sameLedger runtimeLedger uninitialized in
/-- The same issued tree reflects native completion to its independent Source grade. -/
theorem reflects_compiled [FunctionCalls.FaultTokens semanticFaults]
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {rootScope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source rootScope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy
      compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source rootScope reasonAt)
    (coercions : ∀ id node,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [])
    {rootId : ExpressionId}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
    (typed : ExpressionHasType invocation.source context rootId node.type)
    {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation
      invocation.source rootScope rootId reasonAt = .ok rootCode)
    (ports : CallsReady (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted))
    (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
    let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted
    intro scope id lowered certified
    exact CallableIndexedOwnedPreparedStagedRecursiveCallerBounds.reflects
      bridge receiver stagePrepared profile wellFormed runtime covers unique
      actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
      sameLedger runtimeLedger uninitialized stageEq root (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy root syntaxTree policyFor)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root syntaxTree)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root syntaxTree) ports size certified

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCompilerBounds
end
