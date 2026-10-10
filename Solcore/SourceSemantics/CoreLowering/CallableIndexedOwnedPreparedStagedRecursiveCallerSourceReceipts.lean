import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates

/-! Original Source receipts for recursively compiled indirect calls. These
ports recover the actual compatible read and raw child typing before any
recursive argument certificate is constructed. No execution premise is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent Prepared)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem argument_count_of_validation {source : TypedSource} {node : ExpressionNode}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : SourceCompilationPlan.validateIndirectCallMetadata source node callee ids metadata = .ok ()) :
    ids.length = metadata.argumentCount := by
  unfold SourceCompilationPlan.validateIndirectCallMetadata at accepted
  by_cases valid : metadata.hasValidArgumentCoercionPath = true
  · simp only [valid, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨calleeNode, _, accepted⟩ := bind_ok accepted
    cases calleeType : calleeNode.type <;> simp only [calleeType] at accepted <;> try cases accepted
    rename_i parameter result
    obtain ⟨types, _, accepted⟩ := bind_ok accepted
    by_cases count : ids.length = metadata.argumentCount
    · exact count
    · simp [count] at accepted
  · simp [valid, bind, Except.bind] at accepted

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {checked : SourceCoreCompatibleCatalog.Checked}

/-- The actual compatible reader returns the original lookup row unchanged. -/
theorem original_read_metadata
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id) :
    compiler.node = compiler.original ∧
      CompatibleExpressionReads.Metadata checked source id compiler.original compiler.type := by
  have read := compiler.read
  rw [readPolicy] at read
  have actual := CompatibleExpressionReads.metadata_of_read read
  have same := Option.some.inj (actual.found.symm.trans compiler.found)
  exact ⟨same, same ▸ actual⟩

/-- Physical arity comes from validation of the original ordered Source IDs. -/
theorem source_parent
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id) : SourceParent compiler := by
  obtain ⟨_, actual⟩ := original_read_metadata compiler readPolicy
  exact ⟨actual.requirements, actual.coercions, argument_count_of_validation compiler.validated⟩

/-- This inversion precedes recursive argument construction. The callee proof
and ordered raw types come from the original Source typing derivation. -/
theorem original_child_types {context : SourceSemantics.Context}
    (parent : SourceParent compiler)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type) :
    ∃ parameter result sourceTypes,
      ExpressionHasType source context callee (.function parameter result) ∧
      ExpressionsHaveTypes source context ids sourceTypes ∧
      TypeSystem.Ty.productMany sourceTypes = parameter ∧
      compiler.original.type = result := by
  generalize reportedEq : compiler.original.type = reported at parentTyped
  cases parentTyped with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans compiler.found)
    subst actualNode
    rw [compiler.originalForm] at raw
    cases raw with
    | indirectCall calleeTyping argumentsTyping application =>
      have bundle := CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle
        application compiler.argumentCoercions
      have result := requirements.outputPath.foldl_target
      rw [parent.coercions, List.foldl_nil] at result
      exact ⟨_, _, _, calleeTyping, argumentsTyping, bundle, result.symm⟩

/-- The actual reader authenticates the hook's node ID before preparing the
literal callable-policy callsite. -/
theorem prepared {native : SourceCoreGeneralFunctions.CallableContext}
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id)
    (active : TypeSystem.Substitution)
    (actualPolicy : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active) :
    Nonempty (Prepared compiler native) := by
  obtain ⟨same, _⟩ := original_read_metadata compiler readPolicy
  have nodeId : compiler.node.id = id := by
    rw [same]
    exact (lookupExpression?_sound compiler.found).2
  exact Prepared.of_receipt compiler native active actualPolicy nodeId

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts
