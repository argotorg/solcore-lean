import Solcore.SourceSemantics.CoreLowering.LoopBranchReflection
import Solcore.SourceSemantics.CoreLowering.ForInitializerReflection
import Solcore.SourceSemantics.CoreLowering.ForLoopStatementTree

/-! Finite Core executions of the complete static default while/for profile
reconstruct independent finite source executions. Static-tree induction
closes all body/post/initializer contracts; repeated loop iterations use
strictly smaller finite Core derivations. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Reflection

def ReflectsPosition (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (position : Position) (type : Core.Ty) (code : Core.Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects compilation program evidence source reasonAt scope context mode statements type code
  | .initializers items condition post statements =>
      InitializersReflects compilation program evidence source reasonAt scope context items condition post statements type code

theorem Tree.reflects
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ReflectsPosition compilation program evidence source reasonAt scope context position type code := by
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

  | forLoop metadata form _ _ initialIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_for_head metadata.contains form initialIH) tailIH
  | initializersDone condition body post bodyIH =>
      exact reflects_initializers_empty condition body.hasType bodyIH post
  | initializerUninitialized binding extension _ ih =>
      exact reflects_initializers_prepend (.letUninitialized binding extension (.nil ih))
  | initializerInitialized binding extension value _ ih =>
      exact reflects_initializers_prepend (.letInitialized binding extension value (.nil ih))
  | initializerAssign target value _ ih =>
      exact reflects_initializers_prepend (.assign target value (.nil ih))
  | initializerDiscard value _ ih =>
      exact reflects_initializers_prepend (.discard value (.nil ih))

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
