import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionPolicies
import Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueCertificates

/-! The mixed-cell compiler tree retains ordinary literal/read receipts,
actual generalized read wrappers, and the exact ordered indirect children.
No called-body execution or dynamic result appears in a constructor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) (rootFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | plain {id lowered}
      (receipt : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate prepared.fuel
        (.initial checked) source sourceContext (context prepared named).solvedRequirements reasonAt scope id lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | builtin {id lowered}
      (receipt : CellAwareBuiltinValueCertificates.Header prepared source id lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | generalized {id lowered}
      (receipt : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered)
      (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt receipt) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode) (type : node.type = innerNode.type)
      (child : Tree compiled rootFuel source sourceContext reasonAt scope inner lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (type : node.type = .product leftNode.type rightNode.type)
      (leftChild : Tree compiled rootFuel source sourceContext reasonAt scope left first)
      (rightChild : Tree compiled rootFuel source sourceContext reasonAt scope right second) :
      Tree compiled rootFuel source sourceContext reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : Tree compiled rootFuel source sourceContext reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree compiled rootFuel source sourceContext reasonAt scope thenId ⟨type, thenCode⟩)
      (elseTree : Tree compiled rootFuel source sourceContext reasonAt scope elseId ⟨type, elseCode⟩) :
      Tree compiled rootFuel source sourceContext reasonAt scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩
  | call {id callee ids metadata fuel lowered types}
      (compiler : CallableIndirectCallCertificates.Receipt (namedPolicy compiled rootFuel) (namedLowerBody compiled)
        fuel (context prepared named) source scope id callee ids metadata reasonAt lowered)
      (calleeReceipt : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope callee reasonAt compiler.calleeCode)
      (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeReceipt)
      (parent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes)
      (children : ∀ child lowered, (child, lowered) ∈ compiler.entries →
        Tree compiled rootFuel source sourceContext reasonAt scope child lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates
