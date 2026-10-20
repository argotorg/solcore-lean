import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedOrigins

/-! Small state updates used by the actual bounded event traversal. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
namespace Progress

theorem recordExpression (state : State) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) : Progress state (state.recordNode (.expression node)) :=
  appendExpression node rfl (LocalReadEvents.ProgressFields.expression _ _ _ _ _ nonlocal)
    (LocalReadScopeProgress.Progress.recordExpression _ _ (fun name id form => (nonlocal name id form).elim)) (fun below => below)

theorem withLocals (state : State) (locals : List (String × Scheme)) :
    Progress state (state.withLocals locals) :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.refl _) (LocalReadScopeProgress.Progress.refl _)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
