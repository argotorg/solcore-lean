import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderReady

/-! Original Source item typing supplies only the actual header slots. A
successful item identifies the next static context before tail facts are used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderSourceSites
open Frontend SourceInference
open ProtectedForHeader.Stateful.WithReady

variable {source : TypedSource} {control : ControlContext}

def Facts (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (items : List ForItemForm) : Prop :=
  ∃ final, ForItemsHaveType source control context items final

def ItemFacts (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (item : ForItemForm) : Prop :=
  ∃ final, ForItemHasType source control context item final

def ExpressionFacts (source : TypedSource) (context : SourceSemantics.Context)
    (id : ExpressionId) (node : ExpressionNode) : Prop :=
  ExpressionHasType source context id node.type

private theorem stored_expression {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionHasType source context id type)
    (found : source.lookupExpression? id = some node) : ExpressionFacts source context id node := by
  obtain ⟨stored, contains, sourceType⟩ := typing.stored_type
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases same
  change ExpressionHasType source context id node.type
  exact sourceType ▸ typing

private theorem key_typed {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (typed : SourceProjectionsHaveType source context root projections leaf)
    {id : ExpressionId} (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    ∃ type, ExpressionHasType source context id type := by
  induction projections generalizing root leaf with
  | nil => cases typed; cases member
  | cons projection projections ih =>
    cases typed with
    | index head rest =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨_, head⟩
      · exact ih rest tail
    | member _ rest => exact ih rest member

theorem expression {context : SourceSemantics.Context} {item : ForItemForm}
    {id : ExpressionId} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (facts : ItemFacts source control context item) (slot : ExpressionSlot item id)
    (found : source.lookupExpression? id = some node) : ExpressionFacts source context id node := by
  obtain ⟨final, typed⟩ := facts
  cases slot with
  | initialized mono =>
    cases typed with
    | letInitialized typing _ _ _ => exact stored_expression unique typing found
    | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | discard =>
    cases typed with
    | expression typing => exact stored_expression unique typing found
  | projectedBitNotKey member =>
    cases typed with
    | assignBitNot typing =>
      cases typing with
      | intro target _ =>
        cases target with
        | intro _ projections _ =>
          obtain ⟨type, keyTyped⟩ := key_typed projections member
          exact stored_expression unique keyTyped found

theorem item_context {program : Program} {context staticFinal runtimeFinal : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment next : Dynamic.Environment}
    {before after : Dynamic.Heap} {item : ForItemForm}
    (typing : ForItemHasType source control context item staticFinal)
    (executed : Dynamic.ForItemExecutes program context evidence source environment before item runtimeFinal next after) :
    runtimeFinal = staticFinal := by
  cases executed with
  | letUninitialized mono extended allocated =>
    cases typing with
    | letUninitialized _ _ staticExtended => exact (Dynamic.BinderExtends.functional staticExtended extended).symm
  | letInitialized evaluated mono extended allocated =>
    cases typing with
    | letInitialized _ _ _ staticExtended => exact (Dynamic.BinderExtends.functional staticExtended extended).symm
    | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | letInitializedGeneralized captures poly extended allocated =>
    cases typing with
    | letInitialized _ mono _ _ => exact False.elim (poly mono)
    | letInitializedGeneralized _ _ _ _ staticExtended => exact (Dynamic.BinderExtends.functional staticExtended extended).symm
  | expression | assignValue | assignBitNot => cases typing; rfl

theorem sites (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (control : ControlContext) (unique : NodeOccurrencesUnique source) :
    StaticSites (Facts source control) (ItemFacts source control) (ExpressionFacts source)
      (SourceAssignmentHasType source) (SourceBitNotAssignmentValid source) program evidence source where
  head := by
    intro context item rest facts
    obtain ⟨final, typed⟩ := facts
    cases typed with
    | cons head _ => exact ⟨_, head⟩
  expression := expression unique
  assignment := by
    intro context assignment operator rhs facts
    obtain ⟨final, typed⟩ := facts
    cases typed with
    | assignValue typing => exact typing
  snapshot := by
    intro context assignment facts
    obtain ⟨final, typed⟩ := facts
    cases typed with
    | assignBitNot typing => exact typing
  tail := by
    intro context nextContext item rest environment next before after facts executed
    obtain ⟨final, typed⟩ := facts
    cases typed with
    | cons head tail => exact item_context head executed ▸ ⟨_, tail⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderSourceSites
