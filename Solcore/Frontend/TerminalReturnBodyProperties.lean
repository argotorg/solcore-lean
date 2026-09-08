import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.ConditionalReturnBodyProperties

/-! Exact static union laws retain the two original body profiles. Embeddings
preserve the whole optional checker result, including unsupported children. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTerminalReturnBody?_single (table : LocalNameTable) (context : Resolved.Context)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := rfl

theorem elaborateTerminalReturnBody?_conditional (table : LocalNameTable) (context : Resolved.Context)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =
      elaborateConditionalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ := rfl

theorem ReturnBodyElaborates.terminal_complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnBody? table context body = some (core, type) := by
  have accepted := elaboration.complete
  cases elaboration <;> exact accepted

theorem ConditionalReturnBodyElaborates.terminal_complete
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnBody? table context body = some (core, type) := by
  have accepted := elaboration.complete
  cases elaboration
  exact accepted

theorem TerminalReturnBodyElaborates.complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnBody? table context body = some (core, type) := by
  cases elaboration with
  | single child => exact child.terminal_complete
  | conditional child => exact child.terminal_complete

theorem elaborateTerminalReturnBody?_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type)) :
    TerminalReturnBodyElaborates table context body core type := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => simp only [elaborateTerminalReturnBody?, reduceCtorEq] at accepted
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateTerminalReturnBody?, reduceCtorEq] at accepted
      | nil =>
          rcases statement with ⟨statementSpan, payload⟩
          cases payload <;> try simp only [elaborateTerminalReturnBody?, reduceCtorEq] at accepted
          case returnStmt returned => exact .single (elaborateReturnBody?_elaborates accepted)
          case ifThen condition thenBody optionalElse =>
            cases optionalElse with
            | none => simp only [reduceCtorEq] at accepted
            | some elseBody => exact .conditional (elaborateConditionalReturnBody?_elaborates accepted)

theorem elaborateTerminalReturnBody?_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateTerminalReturnBody? table context body = some (core, type) ↔
      TerminalReturnBodyElaborates table context body core type :=
  ⟨elaborateTerminalReturnBody?_elaborates, TerminalReturnBodyElaborates.complete⟩

theorem TerminalReturnBodyElaborates.hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type) :
    TerminalReturnBodyHasType table context body type := by
  cases elaboration with
  | single child => exact .single child.hasType
  | conditional child => exact .conditional child.hasType

theorem TerminalReturnBodyHasType.elaborates_exact {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnBodyHasType table context body type) :
    ∃ core, TerminalReturnBodyElaborates table context body core type := by
  cases typing with
  | single child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .single elaboration⟩
  | conditional child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .conditional elaboration⟩

theorem TerminalReturnBodyHasType.elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnBodyHasType table context body type) :
    ∃ core, elaborateTerminalReturnBody? table context body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateTerminalReturnBody?_sound {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type)) :
    TerminalReturnBodyHasType table context body type :=
  (elaborateTerminalReturnBody?_elaborates accepted).hasType

theorem terminalReturnBodyHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} : TerminalReturnBodyHasType table context body type ↔
      ∃ core, elaborateTerminalReturnBody? table context body = some (core, type) :=
  ⟨TerminalReturnBodyHasType.elaborates, fun ⟨_, accepted⟩ => elaborateTerminalReturnBody?_sound accepted⟩

theorem elaborateTerminalReturnBody?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaborateTerminalReturnBody?_elaborates accepted with
  | single child => exact elaborateReturnBody?_core_hasType child.complete
  | conditional child => exact elaborateConditionalReturnBody?_core_hasType child.complete

theorem TerminalReturnBodyElaborates.result_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : TerminalReturnBodyElaborates table context body leftCore leftType)
    (right : TerminalReturnBodyElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem TerminalReturnBodyHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : TerminalReturnBodyHasType table context body left)
    (second : TerminalReturnBodyHasType table context body right) : left = right := by
  obtain ⟨_, firstElaboration⟩ := first.elaborates_exact
  obtain ⟨_, secondElaboration⟩ := second.elaborates_exact
  exact (firstElaboration.result_unique secondElaboration).2

theorem elaborateTerminalReturnBody?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} : elaborateTerminalReturnBody? table context body = none ↔
      ¬ ∃ type, TerminalReturnBodyHasType table context body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateTerminalReturnBody? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateTerminalReturnBody?_sound result⟩)

end Solcore.Frontend
