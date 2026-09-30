import Solcore.SourceSemantics.CoreLowering.ForLoopStatementTree

/-! Forget the loop continuation while retaining the actual initializer
compiler tree. This projection is used only for faults within initializers. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference

def HeaderPosition (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (position : Position) (type : Core.Ty) (code : Core.Expr) : Prop :=
  match position with
  | .statements _ _ => True
  | .initializers items _ _ _ => ForHeaders.Tree compilation source reasonAt type (fun _ _ _ => True) scope context items code

theorem Tree.header
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code) :
    HeaderPosition compilation source reasonAt scope context position type code := by
  induction tree with
  | initializersDone => exact .nil trivial
  | initializerUninitialized binding extension _ ih => exact .letUninitialized binding extension ih
  | initializerInitialized binding extension value _ ih => exact .letInitialized binding extension value ih
  | initializerAssign target value _ ih => exact .assign target value ih
  | initializerDiscard value _ ih => exact .discard value ih
  | nil | letUninitialized | letInitialized | assign | discard | returnValue | returnUnit | tailExpression
  | block | ifThen | whileLoop | forLoop | breaking | continuing => exact trivial

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
