import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerPolicyInputs

/-! The original contextual bind retains one policy for all child budgets.
Pointwise metadata ports preserve that root callback and its minimum budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedOwnedIndirectCompilerReceipts
open CallableIndexedOwnedIndirectCompilerPolicyInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Profiles belong to the literal selected root policy, rather than an
arbitrary policy whose lowered output happens to agree. -/
structure RootPolicyReceipt (named : Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  selected : ContextualPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    fuel source scope id reasonAt lowered
  sourceCells : selected.policy.sourceCells = some (allocator compiled.indexed named)
  rawLambdaBody : selected.policy.rawLambdaBody = SourceCoreLambdaTemplates.hook
    compiled.indexed.ancestry.templates named.signature.key []
  rawLambdaExpression : selected.policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook
    compiled.indexed.ancestry named.signature.key []
  projectType : selected.policy.projectType = SourceCoreCompatibleDataExpressions.projectType compiled.compatible.checked

/-- Unwrap the actual outer bind once and construct the selected receipt and
all its profiles together. No child contextual acceptance is selected. -/
theorem RootPolicyReceipt.of_accepted
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) source scope id reasonAt = .ok lowered) :
    Nonempty (RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
      fuel source scope id reasonAt lowered) := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  dsimp only at accepted
  change (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key
    |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = .ok lowered at accepted
  rw [record] at accepted
  simp only [Except.mapError, bind, Except.bind] at accepted
  exact ⟨⟨⟨_, _, accepted, rfl, rfl, _, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩⟩

section Pointwise
variable
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- Both fields apply at the actual child occurrence while rootFuel remains
inside the original selected callback. -/
structure PointwiseFor (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) : Prop where
  read : root.selected.policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id
  special : ∀ child budget, (match root.selected.policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower (context compiled.indexed named) child budget source scope id reasonAt) = .ok none

/-- The actual graph selection supplies the callable convention. -/
theorem RootPolicyReceipt.callables :
    root.selected.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      (some compiled.indexed.ancestry.graph.inputs.callable) [] := by
  rw [root.selected.callables]
  rw [compiled.indexed.ancestry.graph.inputs.callableSelected]

private theorem evidence_none_lambda
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (current : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    {source : TypedSource} (scope : SourceCoreLocalCell.Scope)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId}
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller current child budget
      source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]

/-- Genuine lambda metadata excludes only this node's original override gates. -/
theorem lambda_policy
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none) :
    PointwiseFor root source scope id reasonAt := by
  have sameSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals
      (context compiled.indexed named).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  constructor
  · rw [root.selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [representation_read]
  · intro child budget
    rw [root.selected.special_eq, root.selected.special_body]
    have noEvidence := evidence_none_lambda compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized (context compiled.indexed named) child budget scope reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
      found form requirements coercions
    simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary,
      Option.filter_none, noEvidence, form]

/-- Empty raw argument coercions and initializer absence remain independent
conditions at the actual indirect child. -/
theorem indirect_policy
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none) :
    PointwiseFor root source scope id reasonAt := by
  have sameSource := contextualSource_indirect compiled.indexed.base.sourceProgram
    (context compiled.indexed named).plan compiled.indexed.base.locals
    (context compiled.indexed named).owner none found form
  constructor
  · rw [root.selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [representation_read]
  · intro child budget
    rw [root.selected.special_eq, root.selected.special_body]
    have noEvidence := evidence_none_indirect compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized (context compiled.indexed named) child budget scope reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
      found form requirements coercions arguments
    simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary,
      Option.filter_none, noEvidence, form]

end Pointwise
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
