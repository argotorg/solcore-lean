import Solcore.Frontend.TerminalReturnTree

/-! Exact recursive elaboration characterizes the total tree checker. Child
inversion retains both original arms, not just a selected or same-typed Core. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTerminalReturnTree?_single (table : LocalNameTable) (context : Resolved.Context)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := by
  rw [elaborateTerminalReturnTree?]

theorem elaborateTerminalReturnTree?_children
    {table : LocalNameTable} {context : Resolved.Context}
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      elaborateLocalExpression? table context condition = some (conditionCore, .bool) ∧
      elaborateTerminalReturnTree? table context thenBody = some (thenCore, type) ∧
      elaborateTerminalReturnTree? table context elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  rw [elaborateTerminalReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨conditionCore, conditionType⟩, conditionAccepted, remaining⟩ := accepted
  split at remaining
  next conditionBool =>
    change conditionType = .bool at conditionBool
    subst conditionType
    simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨⟨thenCore, thenType⟩, thenAccepted, ⟨elseCore, elseType⟩, elseAccepted, result⟩ := remaining
    split at result
    next sameType =>
      change thenType = elseType at sameType
      subst elseType
      change some (.ifE conditionCore thenCore elseCore, thenType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩
    next different => cases result
  next notBool => cases remaining

theorem TerminalReturnTreeElaborates.complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context body core type) :
    elaborateTerminalReturnTree? table context body = some (core, type) := by
  induction elaboration with
  | single child =>
      have accepted := child.complete
      cases child <;> simpa only [elaborateTerminalReturnTree?] using accepted
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      rw [elaborateTerminalReturnTree?]
      simp [elaborateLocalExpression?_complete resolution lowered typing, thenIH, elseIH]

theorem elaborateTerminalReturnTree?_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type)) :
    TerminalReturnTreeElaborates table context body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTerminalReturnTree?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases rest with
          | cons next rest => simp only [elaborateTerminalReturnTree?, reduceCtorEq] at accepted
          | nil =>
              cases statement with
              | mk statementSpan payload =>
                  cases payload <;> try simp only [elaborateTerminalReturnTree?, reduceCtorEq] at accepted
                  case returnStmt returned => exact .single (elaborateReturnBody?_elaborates accepted)
                  case ifThen condition thenBody optionalElse =>
                    cases optionalElse with
                    | none => simp only [elaborateTerminalReturnTree?, reduceCtorEq] at accepted
                    | some elseBody =>
                        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                          thenAccepted, elseAccepted, rfl⟩ :=
                          elaborateTerminalReturnTree?_children (blockSpan := blockSpan) (ifSpan := statementSpan) accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ :=
                          elaborateLocalExpression?_sound conditionAccepted
                        exact .conditional resolution lowered typing
                          (elaborateTerminalReturnTree?_elaborates thenAccepted)
                          (elaborateTerminalReturnTree?_elaborates elseAccepted)
termination_by sizeOf body

theorem elaborateTerminalReturnTree?_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateTerminalReturnTree? table context body = some (core, type) ↔
      TerminalReturnTreeElaborates table context body core type :=
  ⟨elaborateTerminalReturnTree?_elaborates, TerminalReturnTreeElaborates.complete⟩

end Solcore.Frontend
