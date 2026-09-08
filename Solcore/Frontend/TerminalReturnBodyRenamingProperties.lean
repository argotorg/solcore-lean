import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.ConditionalReturnBodyRenamingProperties

/-! The nonrecursive terminal union preserves exact component elaboration and
all optional checker/runner results under injective identity relabeling. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnBodyElaborates.mapIds {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    TerminalReturnBodyElaborates (LocalNameTable.mapIds mapping table)
      (Resolved.LocalScope.mapIds mapping context) body core type := by
  cases elaboration with
  | single child => exact .single (child.mapIds mapping injective)
  | conditional child => exact .conditional (child.mapIds mapping injective)

theorem elaborateTerminalReturnBody?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (body : Syntax.Block) :
    elaborateTerminalReturnBody? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) body =
      elaborateTerminalReturnBody? table context body := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => rfl
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateTerminalReturnBody?]
      | nil =>
          rcases statement with ⟨statementSpan, payload⟩
          cases payload <;> try rfl
          case returnStmt returned =>
            exact elaborateReturnBody?_mapIds mapping injective table context
              ⟨blockSpan, [⟨statementSpan, .returnStmt returned⟩]⟩
          case ifThen condition thenBody optionalElse =>
            cases optionalElse with
            | none => rfl
            | some elseBody =>
                exact elaborateConditionalReturnBody?_mapIds mapping injective table context
                  ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩

namespace LocalInputs

theorem checkTerminalReturnBody?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (body : Syntax.Block) :
    (inputs.mapIds mapping injective).checkTerminalReturnBody? body = inputs.checkTerminalReturnBody? body := by
  simp only [checkTerminalReturnBody?, mapIds_names, mapIds_context,
    elaborateTerminalReturnBody?_mapIds mapping injective]

/-- Relabeling changes no positional runtime value, including at insufficient fuel. -/
theorem runTerminalReturnBody?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds mapping injective).runTerminalReturnBody? fuel body store =
      inputs.runTerminalReturnBody? fuel body store := by
  simp only [runTerminalReturnBody?, checkTerminalReturnBody?_mapIds,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end LocalInputs
end Solcore.Frontend
