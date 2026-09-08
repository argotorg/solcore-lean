import Solcore.Frontend.TerminalReturnTreeElaboration

/-! Whole recursive source typing and exact elaboration agree without runtime
values. Every original arm contributes independent evidence at every depth. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeElaborates.hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context body core type) :
    TerminalReturnTreeHasType table context body type := by
  induction elaboration with
  | single child => exact .single child.hasType
  | conditional resolution _ typing _ _ thenIH elseIH =>
      exact .conditional (resolution.reflects_type typing) thenIH elseIH

theorem TerminalReturnTreeHasType.elaborates_exact {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnTreeHasType table context body type) :
    ∃ core, TerminalReturnTreeElaborates table context body core type := by
  induction typing with
  | single child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .single elaboration⟩
  | conditional conditionTyping _ _ thenIH elseIH =>
      obtain ⟨resolved, resolution, typed⟩ := conditionTyping.resolves
      obtain ⟨conditionCore, lowered, _⟩ := typed.lowers
      obtain ⟨thenCore, thenElaboration⟩ := thenIH
      obtain ⟨elseCore, elseElaboration⟩ := elseIH
      exact ⟨.ifE conditionCore thenCore elseCore,
        .conditional resolution lowered typed thenElaboration elseElaboration⟩

theorem terminalReturnTreeHasType_iff_elaborates_exact
    {table : LocalNameTable} {context : Resolved.Context} {body : Syntax.Block} {type : Core.Ty} :
    TerminalReturnTreeHasType table context body type ↔
      ∃ core, TerminalReturnTreeElaborates table context body core type :=
  ⟨TerminalReturnTreeHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem TerminalReturnTreeHasType.elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnTreeHasType table context body type) :
    ∃ core, elaborateTerminalReturnTree? table context body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateTerminalReturnTree?_sound {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type)) :
    TerminalReturnTreeHasType table context body type :=
  (elaborateTerminalReturnTree?_elaborates accepted).hasType

theorem terminalReturnTreeHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context} {body : Syntax.Block} {type : Core.Ty} :
    TerminalReturnTreeHasType table context body type ↔
      ∃ core, elaborateTerminalReturnTree? table context body = some (core, type) :=
  ⟨TerminalReturnTreeHasType.elaborates, fun ⟨_, accepted⟩ => elaborateTerminalReturnTree?_sound accepted⟩

theorem elaborateTerminalReturnTree?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  have elaboration := elaborateTerminalReturnTree?_elaborates accepted
  clear accepted
  induction elaboration with
  | single child => exact elaborateReturnBody?_core_hasType child.complete
  | conditional _ lowered typing _ _ thenIH elseIH =>
      exact .ifE (lowered.preserves_type typing) thenIH elseIH

/-- The whole checked tree fixes the exact Core as well as its type. Equal
types alone do not permit a different ordering or choice of return leaves. -/
theorem TerminalReturnTreeElaborates.result_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : TerminalReturnTreeElaborates table context body leftCore leftType)
    (right : TerminalReturnTreeElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem TerminalReturnTreeHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : TerminalReturnTreeHasType table context body left)
    (second : TerminalReturnTreeHasType table context body right) : left = right := by
  obtain ⟨_, firstElaboration⟩ := first.elaborates_exact
  obtain ⟨_, secondElaboration⟩ := second.elaborates_exact
  exact (firstElaboration.result_unique secondElaboration).2

theorem elaborateTerminalReturnTree?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} : elaborateTerminalReturnTree? table context body = none ↔
      ¬ ∃ type, TerminalReturnTreeHasType table context body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateTerminalReturnTree? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateTerminalReturnTree?_sound result⟩)

/-- Only the enclosing block and statement spans change. The original condition
and arbitrarily deep ordered child blocks remain identical. -/
theorem elaborateTerminalReturnTree?_spans (table : LocalNameTable) (context : Resolved.Context)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan otherBlockSpan otherIfSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =
      elaborateTerminalReturnTree? table context
        ⟨otherBlockSpan, [⟨otherIfSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ := by
  simp only [elaborateTerminalReturnTree?]

end Solcore.Frontend
