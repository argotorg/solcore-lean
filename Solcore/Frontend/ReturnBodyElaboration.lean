import Solcore.Frontend.ReturnBodyProperties

/-! Exact independent preparation of a singleton-return body. The expression
rule retains resolved structure, positional lowering, and typing separately;
another Core expression of the same type is not an alternative elaboration. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ReturnBodyElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} :
      ReturnBodyElaborates table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit .unit
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
      (resolution : ResolvesLocalExpression table source resolved)
      (lowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolved core)
      (typing : Resolved.HasType context resolved type) :
      ReturnBodyElaborates table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ core type

theorem ReturnBodyElaborates.complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    elaborateReturnBody? table context body = some (core, type) := by
  cases elaboration with
  | bare => rfl
  | expression resolution lowered typing =>
      exact elaborateLocalExpression?_complete resolution lowered typing

theorem elaborateReturnBody?_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type)) :
    ReturnBodyElaborates table context body core type := by
  cases elaborateReturnBody?_sound accepted with
  | bare =>
      simp only [elaborateReturnBody?, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, _⟩
      exact .bare
  | expression _ =>
      obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
      exact .expression resolution lowered typing

theorem elaborateReturnBody?_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateReturnBody? table context body = some (core, type) ↔
      ReturnBodyElaborates table context body core type :=
  ⟨elaborateReturnBody?_elaborates, ReturnBodyElaborates.complete⟩

theorem ReturnBodyElaborates.hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    ReturnBodyHasType table context body type := by
  cases elaboration with
  | bare => exact .bare
  | expression resolution _ typing => exact .expression (resolution.reflects_type typing)

theorem ReturnBodyHasType.elaborates_exact {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ReturnBodyHasType table context body type) :
    ∃ core, ReturnBodyElaborates table context body core type := by
  obtain ⟨core, accepted⟩ := typing.elaborates
  exact ⟨core, elaborateReturnBody?_elaborates accepted⟩

/-- Exact preparation determines both Core and type, not only type agreement. -/
theorem ReturnBodyElaborates.result_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : ReturnBodyElaborates table context body leftCore leftType)
    (right : ReturnBodyElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

end Solcore.Frontend
