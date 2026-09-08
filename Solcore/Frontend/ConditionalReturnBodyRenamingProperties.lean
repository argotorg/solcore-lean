import Solcore.Frontend.ConditionalReturnBody
import Solcore.Frontend.ReturnBodyRenamingProperties

/-! Injective identity maps retain the original condition, both checked arms,
and exact Core. No owner or runtime-entry layer is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ConditionalReturnBodyElaborates.mapIds
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    ConditionalReturnBodyElaborates (LocalNameTable.mapIds mapping table)
      (Resolved.LocalScope.mapIds mapping context) body core type := by
  cases elaboration with
  | intro resolution lowered typing thenArm elseArm =>
      refine .intro (resolution.mapIds mapping) ?_
        ((Resolved.typing_renameIds_iff mapping injective).mpr typing)
        (thenArm.mapIds mapping injective) (elseArm.mapIds mapping injective)
      rw [Resolved.LocalScope.ids_mapIds]
      exact (Resolved.lowers_renameIds_iff mapping injective).mpr lowered

theorem elaborateConditionalReturnBody?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (body : Syntax.Block) :
    elaborateConditionalReturnBody? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) body =
      elaborateConditionalReturnBody? table context body := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => rfl
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateConditionalReturnBody?]
      | nil =>
          rcases statement with ⟨ifSpan, payload⟩
          cases payload <;> try rfl
          case ifThen condition thenBody optionalElse =>
            cases optionalElse with
            | none => rfl
            | some elseBody =>
                simp only [elaborateConditionalReturnBody?,
                  elaborateLocalExpression?_mapIds mapping injective, elaborateReturnBody?_mapIds mapping injective]

namespace LocalInputs

theorem checkConditionalReturnBody?_mapIds (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) (body : Syntax.Block) :
    (inputs.mapIds mapping injective).checkConditionalReturnBody? body = inputs.checkConditionalReturnBody? body := by
  simp only [checkConditionalReturnBody?, mapIds_names, mapIds_context,
    elaborateConditionalReturnBody?_mapIds mapping injective]

/-- Full optional machine results agree, not only completed values. -/
theorem runConditionalReturnBody?_mapIds (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds mapping injective).runConditionalReturnBody? fuel body store =
      inputs.runConditionalReturnBody? fuel body store := by
  simp only [runConditionalReturnBody?, checkConditionalReturnBody?_mapIds,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end LocalInputs
end Solcore.Frontend
