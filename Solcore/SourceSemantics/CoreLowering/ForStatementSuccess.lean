import Solcore.SourceSemantics.CoreLowering.ForInitializerSuccess
import Solcore.SourceSemantics.CoreLowering.ForLoopStatementTree

/-! Supplied successful source executions of the complete static default
while/for profile produce finite Core executions. Static-tree induction
closes body/post/initializer contracts; loop recursion follows the given
independent finite source derivation. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Default

def SuccessPosition (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (position : Position) (type : Core.Ty) (code : Core.Expr) : Prop :=
  match position with
  | .statements mode statements => Success program evidence source scope context mode statements type code
  | .initializers items condition post statements =>
      InitializersSuccess program evidence source scope context items condition post statements type code

theorem Tree.source_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    SuccessPosition program evidence source scope context position type code := by
  induction tree with
  | nil => exact success_nil program evidence source _ _ _ _
  | breaking _ metadata form => exact success_breaking unique metadata.contains form
  | continuing _ metadata form => exact success_continuing unique metadata.contains form
  | returnUnit _ metadata form => exact success_returnUnit unique metadata.contains form
  | returnValue _ metadata form value => exact success_returnValue unique metadata.contains form value
  | tailExpression metadata form value => exact success_tailExpression unique metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
      exact success_letUninitialized unique metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
      exact success_letInitialized unique metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact success_assign unique metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact success_discard unique metadata.contains form notTail value ih
  | block metadata form _ _ bodyIH tailIH =>
      exact success_scoped unique metadata.contains (by intros; simp [form])
        (success_block_head unique metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition _ _ _ thenIH elseIH tailIH =>
      exact success_scoped unique metadata.contains (by intros; simp [form])
        (success_if_head unique metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition body _ bodyIH tailIH =>
      exact success_scoped unique metadata.contains (by intros; simp [form])
        (success_while_head unique metadata.contains form condition body.hasType bodyIH) tailIH

  | forLoop metadata form _ _ initialIH tailIH =>
      exact success_scoped unique metadata.contains (by intros; simp [form])
        (success_for_head unique metadata.contains form initialIH) tailIH
  | initializersDone condition body post bodyIH =>
      exact success_initializers_empty unique condition body.hasType bodyIH post
  | initializerUninitialized binding extension _ ih =>
      exact success_initializers_prepend (compilation := compilation) (reasonAt := reasonAt) (.letUninitialized binding extension (.nil ih)) unique
  | initializerInitialized binding extension value _ ih =>
      exact success_initializers_prepend (.letInitialized binding extension value (.nil ih)) unique
  | initializerAssign target value _ ih =>
      exact success_initializers_prepend (.assign target value (.nil ih)) unique
  | initializerDiscard value _ ih =>
      exact success_initializers_prepend (.discard value (.nil ih)) unique

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
