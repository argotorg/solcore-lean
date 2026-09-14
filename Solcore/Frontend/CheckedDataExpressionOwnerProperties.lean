import Solcore.Frontend.ClosedSourceOwnerCoreExpressionProperties
import Solcore.Frontend.LocalExpressionTypingProperties

/- A successful data-expression check supplies the original resolution and
lowering stages. Owner transport exposes those stages on both sides while the
checked Core expression and every mapped raw endpoint remain literal. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- A checked closed-data expression transports through every injective owner
map. Besides mapped checker and ID success, the witness records the original
and mapped resolution/lowering stages used by the complete endpoint image. -/
theorem ClosedSourceDataExpression.mapOwners_checked_core_evaluates_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore : Core.Store} {source : Syntax.Expr} {core : Core.Expr}
    {type : Core.Ty} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataExpression source)
    (accepted : elaborateLocalExpression? names context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    elaborateLocalExpression?
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source =
          some (core, type) ∧
      Resolved.LocalScope.ids
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
        Resolved.LocalScope.ids
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) ∧
      ∃ resolved,
        ResolvesLocalExpression names source resolved ∧
        Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core ∧
        ResolvesLocalExpression
          (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) source
          (resolved.renameIds (ownerLocalIdMap mapping)) ∧
        Resolved.Lowers
          (Resolved.LocalScope.ids
            (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment))
          (resolved.renameIds (ownerLocalIdMap mapping)) core ∧
        (ClosedSourceExpressionEvaluates (mapping owner)
          (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
          ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map
            (fun row => (row.1, RuntimeValue.ofCore row.2)))
          (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
        ∃ value finalStore,
          actualValue = RuntimeValue.ofCore value ∧
          actualFinal = finalStore.map RuntimeValue.ofCore ∧
          Core.Evaluates (Resolved.LocalScope.values environment) initialStore
            core value finalStore) := by
  have mappedAccepted :=
    (elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
      (ownerLocalIdMap_injective mapping injective) names context source).trans accepted
  have mappedSameIds : Resolved.LocalScope.ids
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
      Resolved.LocalScope.ids
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) := by
    simpa only [Resolved.LocalScope.ids_mapIds] using
      congrArg (List.map (ownerLocalIdMap mapping)) sameIds
  obtain ⟨resolved, resolution, contextLowered, _⟩ :=
    elaborateLocalExpression?_sound accepted
  have environmentLowered : Resolved.Lowers
      (Resolved.LocalScope.ids environment) resolved core := by
    rw [sameIds]
    exact contextLowered
  have image := fragment.mapOwners_core_evaluates_iff mapping injective
    (owner := owner) (environment := environment) (initialStore := initialStore)
    (actualValue := actualValue) (actualFinal := actualFinal)
    resolution environmentLowered
  exact ⟨mappedAccepted, mappedSameIds, resolved, resolution, environmentLowered,
    image.1, image.2.1, image.2.2⟩

end Solcore.Frontend
