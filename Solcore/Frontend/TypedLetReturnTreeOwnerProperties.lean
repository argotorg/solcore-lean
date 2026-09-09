import Solcore.Frontend.TypedLetReturnTreeProperties
import Solcore.Frontend.LocalTypeInputsOwnerProperties
import Solcore.Frontend.ReturnBodyRenamingProperties

/-! Owner-only relabeling preserves independent recursive provenance and whole
checker results. Fresh tails and both original-scope siblings are transported
without inverse owner maps or inhabitants for static input types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeElaborates.mapOwner
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    TypedLetReturnTreeElaborates types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) body core type := by
  induction elaboration with
  | single child =>
      apply TypedLetReturnTreeElaborates.single
      simpa only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context] using
        (child.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
  | @binding inputs blockSpan letSpan name annotation initializer rest declaredType returnType
      resolved initializerCore tailCore meaning unused resolution lowered typing _ ih =>
      refine .binding (initializerResolved := resolved.renameIds (ownerLocalIdMap mapping))
        meaning ?_ ?_ ?_ ?_ ?_
      · simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing
      · simpa only [LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective] using ih
  | @inferred inputs blockSpan letSpan name initializer rest initializerType returnType
      resolved initializerCore tailCore unused resolution lowered typing _ ih =>
      refine .inferred (inferredType := initializerType)
        (initializerResolved := resolved.renameIds (ownerLocalIdMap mapping))
        ?_ ?_ ?_ ?_ ?_
      · simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing
      · simpa only [LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective] using ih
  | @discard inputs blockSpan statementSpan expression rest discardedType returnType
      resolved expressionCore tailCore resolution lowered typing _ ih =>
      refine .discard (discardedType := discardedType)
        (resolved := resolved.renameIds (ownerLocalIdMap mapping)) ?_ ?_ ?_ ih
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing
  | @conditional inputs blockSpan ifSpan condition thenBody elseBody resolved
      conditionCore thenCore elseCore type resolution lowered typing _ _ thenIH elseIH =>
      refine .conditional (conditionResolved := resolved.renameIds (ownerLocalIdMap mapping))
        ?_ ?_ ?_ thenIH elseIH
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing

theorem TypedLetReturnTreeHasType.mapOwner
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs body type)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    TypedLetReturnTreeHasType types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) body type := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact (elaboration.mapOwner mapping injective).hasType

/-- Recursion on the original syntax also preserves rejection for non-surjective
owner maps. Both conditional arms retain their own original input scope. -/
theorem elaborateTypedLetReturnTree?_mapOwner
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateTypedLetReturnTree? types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)) body =
      elaborateTypedLetReturnTree? types owner inputs body := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTypedLetReturnTree?]
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [elaborateTypedLetReturnTree?]
              case returnStmt returned =>
                cases rest with
                | nil =>
                    simp only [elaborateTypedLetReturnTree?_single,
                      LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context,
                      elaborateReturnBody?_mapIds (ownerLocalIdMap mapping)
                        (ownerLocalIdMap_injective mapping injective)]
                | cons _ _ => simp only [elaborateTypedLetReturnTree?]
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnTree?]
                    | some initializer =>
                        have tailSame (initializerType : Core.Ty) :=
                          elaborateTypedLetReturnTree?_mapOwner mapping injective types owner
                            (inputs.bindFresh owner name.value initializerType) ⟨blockSpan, rest⟩
                        rw [elaborateTypedLetReturnTree?, elaborateTypedLetReturnTree?]
                        simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                        rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                          (ownerLocalIdMap_injective mapping injective)]
                        simp only [LocalNameTable.mapIds, List.map_map, Function.comp_def,
                          ← LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective name.value,
                          tailSame]
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnTree?]
                    | some initializer =>
                        have tailSame (declaredType : Core.Ty) :=
                          elaborateTypedLetReturnTree?_mapOwner mapping injective types owner
                            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
                        rw [elaborateTypedLetReturnTree?, elaborateTypedLetReturnTree?]
                        simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                        rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                          (ownerLocalIdMap_injective mapping injective)]
                        simp only [LocalNameTable.mapIds, List.map_map, Function.comp_def,
                          ← LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective name.value,
                          tailSame]
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [elaborateTypedLetReturnTree?]
                | nil =>
                    cases optionalElse with
                    | none => simp only [elaborateTypedLetReturnTree?]
                    | some elseBody =>
                        rw [elaborateTypedLetReturnTree?, elaborateTypedLetReturnTree?]
                        simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                        rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                          (ownerLocalIdMap_injective mapping injective),
                          elaborateTypedLetReturnTree?_mapOwner mapping injective types owner inputs thenBody,
                          elaborateTypedLetReturnTree?_mapOwner mapping injective types owner inputs elseBody]
              case expression source trailingSemicolon =>
                cases trailingSemicolon with
                | false => simp only [elaborateTypedLetReturnTree?]
                | true =>
                    rw [elaborateTypedLetReturnTree?, elaborateTypedLetReturnTree?]
                    simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                    rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                      (ownerLocalIdMap_injective mapping injective),
                      elaborateTypedLetReturnTree?_mapOwner mapping injective types owner inputs ⟨blockSpan, rest⟩]
termination_by sizeOf body

end Solcore.Frontend
