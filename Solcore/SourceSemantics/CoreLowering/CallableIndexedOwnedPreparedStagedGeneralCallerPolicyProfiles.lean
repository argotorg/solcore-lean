import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.Staging.RecursiveScope

/-! The retained production policy supplies the recursive caller profile.
Every supported Source occurrence has genuine metadata exclusions; the actual
contextual and evidence hooks then delegate before entering their special paths.
Original Source and Code.view need separate global metadata proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
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
  | direct (callee : ExpressionId) (ids : List ExpressionId) (instantiation : DeclarationInstantiation) :
      SupportedForm (.call callee ids (.declaration instantiation))
  | call (callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution) :
      SupportedForm (.call callee ids (.indirect metadata))

private theorem syntax_node {id : ExpressionId}
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id) :
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
  | direct found form _monomorphic _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .direct _ _ _
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
  requirements : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → node.requirements = []
  coercions : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  directCaller : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → named.specialized.assumptions = []
  localRead : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

structure MetadataOn (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) (allowed : ExpressionId → Prop) : Prop where
  requirements : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → node.requirements = []
  coercions : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  directCaller : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → named.specialized.assumptions = []
  localRead : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

/-- Native literals keep their genuine selected evidence rows. Their compiler
validator authenticates those rows; other admitted expressions retain empty
requirements. This is a metadata condition, not an execution premise. -/
structure NativeMetadataFor (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) : Prop where
  requirements : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution
  coercions : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  directCaller : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → named.specialized.assumptions = []
  localRead : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

structure NativeMetadataOn (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) (allowed : ExpressionId → Prop) : Prop where
  requirements : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution
  coercions : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  directCaller : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → named.specialized.assumptions = []
  localRead : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

theorem NativeMetadataFor.of_ordinary (metadata : MetadataFor prepared named source) :
    NativeMetadataFor prepared named source :=
  ⟨fun id tree node found => .inl (metadata.requirements id tree node found),
    metadata.coercions, metadata.initializer, metadata.arguments, metadata.directCaller, metadata.localRead⟩

theorem NativeMetadataOn.of_ordinary {allowed : ExpressionId → Prop}
    (metadata : MetadataOn prepared named source allowed) : NativeMetadataOn prepared named source allowed :=
  ⟨fun id reached tree node found => .inl (metadata.requirements id reached tree node found),
    metadata.coercions, metadata.initializer, metadata.arguments, metadata.directCaller, metadata.localRead⟩

theorem NativeMetadataFor.on (metadata : NativeMetadataFor prepared named source)
    (allowed : ExpressionId → Prop) : NativeMetadataOn prepared named source allowed :=
  ⟨fun id _ tree => metadata.requirements id tree,
   fun id _ tree => metadata.coercions id tree,
   fun id _ tree => metadata.initializer id tree,
   fun id _ tree => metadata.arguments id tree,
   fun id _ tree => metadata.directCaller id tree,
   fun id _ tree => metadata.localRead id tree⟩

theorem MetadataFor.on (metadata : MetadataFor prepared named source)
    (allowed : ExpressionId → Prop) : MetadataOn prepared named source allowed :=
  ⟨fun id _ tree => metadata.requirements id tree,
   fun id _ tree => metadata.coercions id tree,
   fun id _ tree => metadata.initializer id tree,
   fun id _ tree => metadata.arguments id tree,
   fun id _ tree => metadata.directCaller id tree,
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
  | unary | binary | conditional | group | constructor | direct => simp [SourceCoreGeneralFunctions.contextualSource, found, form]
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
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = [])
    (directClosed : ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → caller.assumptions = []) :
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
    | direct callee ids instantiation =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, requirements, coercions,
        directClosed callee ids instantiation form]
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
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id)
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
    (metadata.arguments id tree node found) (metadata.directCaller id tree node found)
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | unary | binary | conditional | group | constructor | direct => rfl
  | tuple => rfl
  | call => rfl

theorem recipe_policy_for_native
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : NativeMetadataFor prepared named source)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor policy (context prepared named)
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor policy (context prepared named)
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
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
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id)
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
    (metadata.arguments id admitted tree node found) (metadata.directCaller id admitted tree node found)
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id admitted tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id admitted tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | unary | binary | conditional | group | constructor | direct => rfl
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn policy (context prepared named)
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn policy (context prepared named)
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn code.policy code.compilation
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn code.policy code.compilation
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) function.source originalScope originalReasonAt ∧
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
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
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) child.source scope reasonAt := by
  rw [stages.source selected]
  exact retained_policy_for retained metadata scope reasonAt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
