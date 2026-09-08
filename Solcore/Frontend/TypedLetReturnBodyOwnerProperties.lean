import Solcore.Frontend.TypedLetReturnBodyProperties
import Solcore.Frontend.LocalTypeInputsOwnerProperties
import Solcore.Frontend.TerminalReturnTreeRenamingProperties

/-! Owner-only relabeling preserves exact typed-prefix provenance and every
checker result. Fresh allocation commutes on the complete supplied scope;
no inverse owner map or runtime inhabitants are required. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyElaborates.mapOwner
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs body core type)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    TypedLetReturnBodyElaborates types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) body core type := by
  induction elaboration with
  | terminal child =>
      apply TypedLetReturnBodyElaborates.terminal
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

theorem TypedLetReturnBodyHasType.mapOwner
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    TypedLetReturnBodyHasType types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) body type := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact (elaboration.mapOwner mapping injective).hasType

/-- Structural recursion also preserves rejection under non-surjective owner
maps. Initializers retain their old scope and tails their freshly extended one. -/
theorem elaborateTypedLetReturnBody?_mapOwner
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateTypedLetReturnBody? types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)) body =
      elaborateTypedLetReturnBody? types owner inputs body := by
  have treeSame := elaborateTerminalReturnTree?_mapIds (ownerLocalIdMap mapping)
    (ownerLocalIdMap_injective mapping injective) inputs.names inputs.context
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTypedLetReturnBody?, LocalTypeInputs.mapIds_names,
          LocalTypeInputs.mapIds_context, treeSame]
      | cons statement rest =>
          cases statement with
          | mk letSpan payload =>
              cases payload <;> try (solve | simp only [elaborateTypedLetReturnBody?,
                LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context,
                treeSame])
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none => simp only [elaborateTypedLetReturnBody?, LocalTypeInputs.mapIds_names,
                    LocalTypeInputs.mapIds_context, treeSame]
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnBody?, LocalTypeInputs.mapIds_names,
                        LocalTypeInputs.mapIds_context, treeSame]
                    | some initializer =>
                        have tailSame (declaredType : Core.Ty) :=
                          elaborateTypedLetReturnBody?_mapOwner mapping injective types owner
                            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
                        rw [elaborateTypedLetReturnBody?, elaborateTypedLetReturnBody?]
                        simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                        rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                          (ownerLocalIdMap_injective mapping injective)]
                        simp only [LocalNameTable.mapIds, List.map_map, Function.comp_def,
                          ← LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective name.value,
                          tailSame]
termination_by body.value.length

end Solcore.Frontend
