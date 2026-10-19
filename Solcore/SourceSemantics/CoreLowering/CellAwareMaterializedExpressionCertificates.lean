import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionPolicies
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates

/-! The compiler tree retains actual generalized read wrappers, transparent
groups and ordered product children. Its static receipts contain no assumed
execution or dynamic result. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCertificates
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) (rootFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
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

theorem Tree.ordinary {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    {compiled : Compilation prepared named diagnostics code} {rootFuel : Nat}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree compiled rootFuel source sourceContext reasonAt scope id lowered) :
    CellAwareNamedExpressionCertificates.Tree compiled rootFuel source sourceContext reasonAt scope id lowered := by
  induction tree with
  | generalized receipt recipe => exact .generalized receipt recipe
  | group metadata form found type _ child => exact .group metadata form found type child
  | pair metadata form leftFound rightFound type _ _ left right =>
    exact .pair metadata form leftFound rightFound type left right

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCertificates
