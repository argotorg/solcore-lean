import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderSourceSites

/-! Original checked header typing determines each actual suffix context.
These facts contain no header execution or child meaning assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
open Frontend SourceInference

abbrev Facts (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (items : List ForItemForm) : Prop :=
  ∃ final, ForItemsHaveType source control context items final

variable {source : TypedSource} {control : ControlContext}
  {context nextContext : SourceSemantics.Context} {rest : List ForItemForm}

theorem absent {binder : TypedBinder}
    (facts : Facts source control context (.letDecl binder none :: rest))
    (extended : BinderExtends source.owner context binder nextContext) :
    Facts source control nextContext rest := by
  obtain ⟨final, typed⟩ := facts
  cases typed with
  | cons head tail =>
      cases head with
      | letUninitialized _ _ actual =>
          cases extended
          cases actual
          exact ⟨final, tail⟩

theorem initialized {binder : TypedBinder} {initializer : ExpressionId}
    (facts : Facts source control context (.letDecl binder (some initializer) :: rest))
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext) :
    Facts source control nextContext rest := by
  obtain ⟨final, typed⟩ := facts
  cases typed with
  | cons head tail =>
      cases head with
      | letInitialized _ _ _ actual =>
          cases extended
          cases actual
          exact ⟨final, tail⟩
      | letInitializedGeneralized polymorphic _ _ _ _ =>
          exact False.elim (polymorphic monomorphic)

theorem expression {id : ExpressionId}
    (facts : Facts source control context (.expression id :: rest)) :
    Facts source control context rest := by
  obtain ⟨final, typed⟩ := facts
  cases typed with
  | cons head tail =>
      cases head
      exact ⟨final, tail⟩

theorem assignment {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp}
    {rhs : ExpressionId}
    (facts : Facts source control context (.assignValue assignment operator rhs :: rest)) :
    SourceAssignmentHasType source context assignment operator rhs ∧
    Facts source control context rest := by
  obtain ⟨final, typed⟩ := facts
  cases typed with
  | cons head tail =>
      cases head with
      | assignValue actual => exact ⟨actual, final, tail⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
