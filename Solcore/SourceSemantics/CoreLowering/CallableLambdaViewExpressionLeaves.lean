import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductTree
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyCertificates

/-! Static expression leaves retain their complete occurrence metadata under
local edits outside the reached body. Source binders are transported through
the actual metadata view, preserving lazy mapping encodings and raw types.
No independent source typing derivation or compiler equation is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewExpressionLeaves
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)

include edited avoids

theorem metadata {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId}
    {node : ExpressionNode} {type : Ty} (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionReads.Metadata checked source id node type) :
    CompatibleExpressionReads.Metadata checked view id node type :=
  ⟨(expression_lookup edited avoids reached).symm.trans receipt.found,
    receipt.owner.trans edited.metadata.owner, receipt.requirements, receipt.coercions, receipt.projected⟩

theorem literal {solved : List SolvedRequirement} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionLiterals.Certificate solved source id lowered) :
    CompatibleExpressionLiterals.Certificate solved view id lowered := by
  obtain ⟨node, found, value⟩ := receipt
  exact ⟨node, (expression_lookup edited avoids reached).symm.trans found, value⟩

/-- The same read certificate keeps its declared binder, actual scope index,
quoted lazy default and emitted code. Only its source lookup receipts change. -/
def read {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionReads.Certificate fuel values source scope id reason code) :
    CompatibleExpressionReads.Certificate fuel values view scope id reason code where
  node := receipt.node
  type := receipt.type
  binder := receipt.binder
  name := receipt.name
  declared := receipt.declared
  index := receipt.index
  metadata := metadata edited avoids reached receipt.metadata
  form := receipt.form
  binderOwner := receipt.binderOwner.trans edited.metadata.owner
  slot := receipt.slot
  declaration := (rootBinder edited.metadata receipt.binder).symm.trans receipt.declaration
  emitted := receipt.emitted

theorem read_binding {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    {context : SourceSemantics.Context} (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
    (binding : CompatibleExpressionReads.StaticBinding receipt context) :
    CompatibleExpressionReads.StaticBinding (read edited avoids reached receipt) context :=
  ⟨binding.declared, binding.occurrence⟩

theorem loweredRead {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context}
    (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered) :
    CompatibleExpressionReads.LoweredRead fuel values view context reasonAt scope id lowered := by
  obtain ⟨certificate, type, binding⟩ := receipt
  exact ⟨read edited avoids reached certificate, type, read_binding edited avoids reached certificate binding⟩

theorem proxy {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered) :
    CompatibleExpressionProxies.Certificate values view scope id lowered := by
  cases receipt with
  | proxy header =>
    exact .proxy ⟨metadata edited avoids reached header.metadata, header.form, header.sourceType,
      header.identity, header.original, header.registered⟩

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewExpressionLeaves
