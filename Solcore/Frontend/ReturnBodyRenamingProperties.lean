import Solcore.Frontend.ReturnBodyElaboration
import Solcore.Frontend.LocalExpressionRenamingSemantics
import Solcore.Frontend.LocalInputsRenaming

/-! Body-level identity relabeling is independent of runtime-function entry.
Exact Core, type, rejection, and same-fuel machine results are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyElaborates.mapIds {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    ReturnBodyElaborates (LocalNameTable.mapIds mapping table)
      (Resolved.LocalScope.mapIds mapping context) body core type := by
  cases elaboration with
  | bare => exact .bare
  | expression resolution lowered typing =>
      refine .expression (resolution.mapIds mapping) ?_
        ((Resolved.typing_renameIds_iff mapping injective).mpr typing)
      rw [Resolved.LocalScope.ids_mapIds]
      exact (Resolved.lowers_renameIds_iff mapping injective).mpr lowered

/-- Both accepted and rejected singleton checks retain the exact optional result. -/
theorem elaborateReturnBody?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (body : Syntax.Block) :
    elaborateReturnBody? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) body =
      elaborateReturnBody? table context body := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => rfl
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateReturnBody?]
      | nil =>
          rcases statement with ⟨returnSpan, payload⟩
          cases payload <;> try rfl
          case returnStmt returned =>
            cases returned with
            | none => rfl
            | some source => exact elaborateLocalExpression?_mapIds mapping injective table context source

namespace LocalInputs

theorem checkReturnBody?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (body : Syntax.Block) :
    (inputs.mapIds mapping injective).checkReturnBody? body = inputs.checkReturnBody? body := by
  simp only [checkReturnBody?, mapIds_names, mapIds_context, elaborateReturnBody?_mapIds mapping injective]

/-- Values and exact suspended states agree at any fuel, with no acceptance premise. -/
theorem runReturnBody?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds mapping injective).runReturnBody? fuel body store = inputs.runReturnBody? fuel body store := by
  simp only [runReturnBody?, checkReturnBody?_mapIds, mapIds_environment, Resolved.LocalScope.values_mapIds]

end LocalInputs
end Solcore.Frontend
