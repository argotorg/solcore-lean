import Solcore.Frontend.TerminalReturnTreeRunner
import Solcore.Frontend.ReturnBodyRenamingProperties

/-! Injective identity relabeling retains all recursive source children, exact
Core and complete same-fuel results without importing runtime-function entry. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeElaborates.mapIds {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context body core type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    TerminalReturnTreeElaborates (LocalNameTable.mapIds mapping table)
      (Resolved.LocalScope.mapIds mapping context) body core type := by
  induction elaboration with
  | single child => exact .single (child.mapIds mapping injective)
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      refine .conditional (resolution.mapIds mapping) ?_
        ((Resolved.typing_renameIds_iff mapping injective).mpr typing) thenIH elseIH
      rw [Resolved.LocalScope.ids_mapIds]
      exact (Resolved.lowers_renameIds_iff mapping injective).mpr lowered

/-- Structural recursion retains failures as well as successful exact Core. -/
theorem elaborateTerminalReturnTree?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (body : Syntax.Block) :
    elaborateTerminalReturnTree? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) body =
      elaborateTerminalReturnTree? table context body := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTerminalReturnTree?]
      | cons statement rest =>
          cases rest with
          | cons next rest => simp only [elaborateTerminalReturnTree?]
          | nil =>
              cases statement with
              | mk statementSpan payload =>
                  cases payload <;> try simp only [elaborateTerminalReturnTree?]
                  case returnStmt returned =>
                    exact elaborateReturnBody?_mapIds mapping injective table context
                      ⟨blockSpan, [⟨statementSpan, .returnStmt returned⟩]⟩
                  case ifThen condition thenBody optionalElse =>
                    cases optionalElse with
                    | none => simp only [elaborateTerminalReturnTree?]
                    | some elseBody =>
                        rw [elaborateTerminalReturnTree?, elaborateTerminalReturnTree?]
                        rw [elaborateLocalExpression?_mapIds mapping injective,
                          elaborateTerminalReturnTree?_mapIds mapping injective table context thenBody,
                          elaborateTerminalReturnTree?_mapIds mapping injective table context elseBody]
termination_by sizeOf body

namespace LocalInputs

theorem checkTerminalReturnTree?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (body : Syntax.Block) :
    (inputs.mapIds mapping injective).checkTerminalReturnTree? body = inputs.checkTerminalReturnTree? body := by
  simp only [checkTerminalReturnTree?, mapIds_names, mapIds_context,
    elaborateTerminalReturnTree?_mapIds mapping injective]

/-- Every optional result agrees, including actual checkpoints at insufficient
fuel. Relabeling does not reverse or otherwise reorder positional values. -/
theorem runTerminalReturnTree?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds mapping injective).runTerminalReturnTree? fuel body store =
      inputs.runTerminalReturnTree? fuel body store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?_mapIds,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end LocalInputs
end Solcore.Frontend
