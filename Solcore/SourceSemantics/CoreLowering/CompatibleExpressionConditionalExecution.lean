import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveExecution

/-! Conditional helpers preserve the actual inserted Bool slot. They require
no store restriction and never evaluate the unselected branch. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
open Core

theorem choose_rename (type : Ty) (condition thenCode elseCode : Expr) (ξ : Renaming) :
    (LocalControl.choose type condition thenCode elseCode).rename ξ =
      LocalControl.choose type (condition.rename ξ) (thenCode.rename ξ) (elseCode.rename ξ) := by
  simp [LocalControl.choose, LanguageResult.bind, Expr.rename,
    Renaming.lift]

theorem choose_branch_evaluated {environment : Environment} {store finalStore : Store}
    {flag : Bool} {thenCode elseCode : Expr} {value : Value}
    (evaluated : Evaluates (.bool flag :: environment) store
      (.ifE (.var 0) (thenCode.weakenAt 0) (elseCode.weakenAt 0)) value finalStore) :
    Evaluates (.bool flag :: environment) store ((if flag then thenCode else elseCode).weakenAt 0) value finalStore := by
  cases evaluated with
  | ifTrue condition branch =>
    cases condition with
    | var selected => cases selected; exact branch
  | ifFalse condition branch =>
    cases condition with
    | var selected => cases selected; exact branch

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
