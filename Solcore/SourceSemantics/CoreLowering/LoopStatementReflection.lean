import Solcore.SourceSemantics.CoreLowering.LoopBranchReflection
import Solcore.SourceSemantics.CoreLowering.LoopWhileReflection

/-! Finite Core executions of the complete static default while profile
reconstruct independent finite source executions. Static-tree induction
closes all body contracts; repeated while iterations use the strictly smaller
finite derivation established in `LoopFiniteReflection`. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Reflection

theorem Tree.reflects
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {mode : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context mode statements type code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    Reflects compilation program evidence source reasonAt scope context mode statements type code := by
  induction tree with
  | nil => exact reflects_nil compilation program evidence source reasonAt _ _ _ _
  | breaking _ metadata form => exact reflects_breaking metadata.contains form
  | continuing _ metadata form => exact reflects_continuing metadata.contains form
  | returnUnit _ metadata form => exact reflects_returnUnit metadata.contains form
  | returnValue _ metadata form value => exact reflects_returnValue metadata.contains form value
  | tailExpression metadata form value => exact reflects_tailExpression metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
      exact reflects_letUninitialized metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
      exact reflects_letInitialized metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact reflects_assign metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact reflects_discard metadata.contains form notTail value ih
  | block metadata form _ _ bodyIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_block_head metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition _ _ _ thenIH elseIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_if_head metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition body _ bodyIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_while_head metadata.contains form condition body.hasType bodyIH) tailIH

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
