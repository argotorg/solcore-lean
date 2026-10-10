import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallTypeReceipts

/-! Original indirect Source typing fixes the raw callee and argument bundle
before selecting any runtime function leaf. Empty compiler output coercions
retain the same raw result. Physical argument count remains independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}

include compiler in
/-- These facts come from the accepted parent and its actual ordered compiler
Tree. No closure representation, application trace or body law is used. -/
theorem original_rows
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode) :
    ∃ parameter result,
      calleeNode.type = .function parameter result ∧
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
      have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
        unique calleeFound calleeTyping
      have row := CallableIndexedOwnedContextualInitializedClosureReceipts.source_types_at_tree
        unique tree argumentsTyping
      have bundle := CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle
        application compiler.argumentCoercions
      have result := requirements.outputPath.foldl_target
      rw [parent.coercions, List.foldl_nil] at result
      exact ⟨_, _, reported, row ▸ argumentsTyping, by simpa only [← row] using bundle, result.symm⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
