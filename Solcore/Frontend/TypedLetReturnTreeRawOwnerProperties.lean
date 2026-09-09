import Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties
import Solcore.Frontend.LocalExpressionEvaluatorProperties
import Solcore.Frontend.LocalExpressionCostInvariance
import Solcore.Frontend.LocalOwnerRenaming

/-! Raw owner covariance preserves complete direct results and independent
paths on arbitrary caller rows. No checking, typing, uniqueness or alignment
premise is introduced, and owner maps need not be surjective. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem expression_mapIds
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (table : LocalNameTable) (environment : Resolved.Environment) (source : Syntax.Expr) :
    evaluateLocalExpressionWithCost? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) source =
      evaluateLocalExpressionWithCost? table environment source := by
  cases original : evaluateLocalExpressionWithCost? table environment source with
  | none =>
      cases mapped : evaluateLocalExpressionWithCost? (LocalNameTable.mapIds mapping table)
          (Resolved.LocalScope.mapIds mapping environment) source with
      | none => rfl
      | some pair =>
          have impossible := evaluateLocalExpressionWithCost?_complete
            ((localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mp
              (evaluateLocalExpressionWithCost?_sound mapped []))
          rw [original] at impossible
          cases impossible
  | some pair =>
      exact evaluateLocalExpressionWithCost?_complete
        ((localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mpr
          (evaluateLocalExpressionWithCost?_sound original []))

private theorem fresh_mapOwner
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (owner : Resolved.DeclarationId) (table : LocalNameTable) :
    Resolved.freshLocalId (mapping owner)
        ((LocalNameTable.mapIds (ownerLocalIdMap mapping) table).map Prod.snd) =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner (table.map Prod.snd)) := by
  simpa only [LocalNameTable.mapIds, List.map_map, Function.comp_def, ownerLocalIdMap,
    Resolved.freshLocalId_owner] using
    Resolved.freshLocalId_map_owner mapping injective owner (table.map Prod.snd)

/-- Relabeling both raw tables preserves success and absence, including strict
initializers and only the actual selected arm. Source and values are unchanged. -/
theorem evaluateTypedLetReturnTreeWithCost?_mapOwner
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (owner : Resolved.DeclarationId)
    (table : LocalNameTable) (environment : Resolved.Environment) (body : Syntax.Block) :
    evaluateTypedLetReturnTreeWithCost? (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) body =
      evaluateTypedLetReturnTreeWithCost? owner table environment body := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [evaluateTypedLetReturnTreeWithCost?]
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [evaluateTypedLetReturnTreeWithCost?]
              case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    cases returned with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                    | some source =>
                        simpa only [evaluateTypedLetReturnTreeWithCost?] using
                          expression_mapIds (ownerLocalIdMap mapping)
                            (ownerLocalIdMap_injective mapping injective) table environment source
              case letDecl name optionalType optionalInitializer =>
                cases optionalInitializer with
                | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                | some initializer =>
                    have tailSame (boundValue : Core.Value) :
                        evaluateTypedLetReturnTreeWithCost? (mapping owner)
                          ((name.value, Resolved.freshLocalId (mapping owner)
                            ((LocalNameTable.mapIds (ownerLocalIdMap mapping) table).map Prod.snd)) ::
                              LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
                          ((Resolved.freshLocalId (mapping owner)
                            ((LocalNameTable.mapIds (ownerLocalIdMap mapping) table).map Prod.snd), boundValue) ::
                              Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) ⟨blockSpan, rest⟩ =
                        evaluateTypedLetReturnTreeWithCost? owner
                          ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
                          ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment) ⟨blockSpan, rest⟩ := by
                      rw [fresh_mapOwner mapping injective owner table]
                      simpa only [LocalNameTable.mapIds, Resolved.LocalScope.mapIds, List.map_cons] using
                        evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner
                          ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
                          ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment) ⟨blockSpan, rest⟩
                    rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                      expression_mapIds (ownerLocalIdMap mapping)
                        (ownerLocalIdMap_injective mapping injective)]
                    simp only [tailSame]
              case expression source terminated =>
                cases terminated with
                | false => simp only [evaluateTypedLetReturnTreeWithCost?]
                | true =>
                    rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                      expression_mapIds (ownerLocalIdMap mapping)
                        (ownerLocalIdMap_injective mapping injective),
                      evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner table environment ⟨blockSpan, rest⟩]
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    cases optionalElse with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                    | some elseBody =>
                        rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                          expression_mapIds (ownerLocalIdMap mapping)
                            (ownerLocalIdMap_injective mapping injective),
                          evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner table environment thenBody,
                          evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner table environment elseBody]
termination_by sizeOf body

/-- Both stores and the exact independent cost are retained; no unrelated
final store is licensed by the store-free executable equality. -/
theorem typedLetReturnTreeEvaluatesWithCost_mapOwner_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    TypedLetReturnTreeEvaluatesWithCost (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore body value finalStore cost ↔
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  rw [typedLetReturnTreeEvaluatesWithCost_iff_evaluate, typedLetReturnTreeEvaluatesWithCost_iff_evaluate,
    evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective]

theorem typedLetReturnTreeEvaluates_mapOwner_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {initialStore finalStore : Core.Store} {value : Core.Value} :
    TypedLetReturnTreeEvaluates (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore body value finalStore ↔
      TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  rw [typedLetReturnTreeEvaluates_iff_exists_cost, typedLetReturnTreeEvaluates_iff_exists_cost]
  exact exists_congr fun _ => typedLetReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective

end Solcore.Frontend
