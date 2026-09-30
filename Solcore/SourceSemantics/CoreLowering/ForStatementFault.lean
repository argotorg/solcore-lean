import Solcore.SourceSemantics.CoreLowering.ForInitializerFault
import Solcore.SourceSemantics.CoreLowering.ForInitializerHeader
import Solcore.SourceSemantics.CoreLowering.ForStatementSuccess

/-! Static-tree induction discharges every body/post/initializer premise for
supplied finite source faults in the complete default while/for profile. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Default

def FaultPosition (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (position : Position) (type : Core.Ty) (code : Core.Expr) : Prop :=
  match position with
  | .statements mode statements => Fault compilation program evidence source reasonAt scope context mode statements type code
  | .initializers items condition post statements =>
      InitializersFault compilation program evidence source reasonAt scope context items condition post statements type code

/-- Whole-list fault correspondence, including successful earlier iterations.
The only dynamic premise is the complete independent source fault derivation. -/
theorem Tree.source_fault
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    FaultPosition compilation program evidence source reasonAt scope context position type code := by
  induction tree with
  | nil => exact fault_nil compilation program evidence source reasonAt _ _ _ _
  | breaking _ metadata form => exact fault_breaking unique metadata.contains form
  | continuing _ metadata form => exact fault_continuing unique metadata.contains form
  | returnUnit _ metadata form => exact fault_returnUnit unique metadata.contains form
  | returnValue _ metadata form value => exact fault_returnValue unique metadata.contains form value
  | tailExpression metadata form value => exact fault_tailExpression unique metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
    exact fault_letUninitialized unique metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
    exact fault_letInitialized unique metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact fault_assign unique metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact fault_discard unique metadata.contains form notTail value ih
  | block metadata form body _ bodyIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_block_head unique metadata.contains form (body.source_success unique program evidence))
      (fault_block_head unique metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition thenBody elseBody _ thenIH elseIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_if_head unique metadata.contains form condition
        (thenBody.source_success unique program evidence) (elseBody.source_success unique program evidence))
      (fault_if_head unique metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition loopBody _ bodyIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_while_head unique metadata.contains form condition loopBody.hasType (loopBody.source_success unique program evidence))
      (fault_while_head unique metadata.contains form condition loopBody.hasType
        (loopBody.source_success unique program evidence) bodyIH) tailIH

  | forLoop metadata form initial _ initialIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_for_head unique metadata.contains form (initial.source_success unique program evidence))
      (fault_for_head unique metadata.contains form initial.header initialIH) tailIH
  | initializersDone condition body post bodyIH =>
    exact fault_initializers_empty unique condition body.hasType (body.source_success unique program evidence) bodyIH post
  | initializerUninitialized binding extension _ ih =>
    exact fault_initializers_prepend (.letUninitialized binding extension (.nil ih)) unique
  | initializerInitialized binding extension value _ ih =>
    exact fault_initializers_prepend (.letInitialized binding extension value (.nil ih)) unique
  | initializerAssign target value _ ih =>
    exact fault_initializers_prepend (.assign target value (.nil ih)) unique
  | initializerDiscard value _ ih =>
    exact fault_initializers_prepend (.discard value (.nil ih)) unique

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
