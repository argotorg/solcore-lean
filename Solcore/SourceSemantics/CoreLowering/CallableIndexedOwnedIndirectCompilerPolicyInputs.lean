import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerReceipts

/-! The selected contextual callback delegates an ordinary indirect node using
its actual Source and metadata. Exact initializer absence and empty argument
coercions remain genuine static inputs at this occurrence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerPolicyInputs
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedOwnedIndirectCompilerReceipts

/-- Contextual local normalization leaves the actual indirect Source intact. -/
theorem contextualSource_indirect
    (program : CheckedProgram) (plan : SourceCompilationPlan.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared)
    {source : TypedSource} {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata)) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, found, form]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Allocator and lambda hooks preserve the original compatible read field. -/
theorem representation_read (named : Named) :
    ((representation compiled.indexed).atContext named.signature.key []).expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked := by
  rfl

/-- The original evidence gate returns none at this exact metadata, before
performing owner or authenticated declaration checks. -/
theorem evidence_none_indirect
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    {source : TypedSource} (scope : SourceCoreLocalCell.Scope)
    {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode}
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child budget source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions, arguments]

section Policy
variable
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode}

/-- Both policy agreements follow from the same selected callback and genuine
pointwise metadata, without first constructing an indirect compiler receipt. -/
theorem policy_of_indirect_metadata
    (selected : ContextualPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
      fuel source scope id reasonAt lowered)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none) :
    PolicyFor selected := by
  have sameSource := contextualSource_indirect compiled.indexed.base.sourceProgram
    (context compiled.indexed named).plan compiled.indexed.base.locals
    (context compiled.indexed named).owner none found form
  constructor
  · rw [selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [representation_read]
  · intro child budget
    rw [selected.special_eq, selected.special_body]
    have noEvidence := evidence_none_indirect compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized (context compiled.indexed named) child budget scope reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
      found form requirements coercions arguments
    simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary,
      Option.filter_none, noEvidence, form]

end Policy

section Contextual
variable
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (factory : Factory caller diagnostics namedCode compilation source sourceContext evidence scope administrative certificates)
    (native : SourceCoreGeneralFunctions.CallableContext)
    {fuel : Nat} {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}

/-- The accepted contextual compiler chooses its actual policy once. Its read
and delegation inputs are derived internally from the same Source occurrence. -/
theorem contextual_receipt_of_indirect_metadata
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan caller.named.signature.key = .ok caller.named.specialized)
    (nativeContext : compiled.indexed.base.callableContext = some native)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (typed : ExpressionHasType source sourceContext id node.type)
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext caller.named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed caller.named)
      compiled.indexed.base.callableContext none none (fuel + 1) source scope id reasonAt = .ok lowered) :
    Nonempty (ContextualReceipt factory native (fuel := fuel) (id := id) (callee := callee) (ids := ids)
      (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered)) := by
  exact ContextualReceipt.of_accepted factory native record nativeContext found form typed unique accepted
    (fun selected => policy_of_indirect_metadata selected found form requirements coercions arguments ordinary)

end Contextual
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerPolicyInputs
