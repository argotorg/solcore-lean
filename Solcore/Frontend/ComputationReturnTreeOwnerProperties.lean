import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.LocalTypeInputsOwnerProperties

/-! Owner-only relabeling preserves independent shared-body evidence and the
whole optional checker result. Reflection remembers the original supplied
inputs; fresh tails use existing commutation, without an inverse owner map. -/

set_option autoImplicit false
namespace Solcore.Frontend

variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}

private theorem child_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {inputs : LocalTypeInputs} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    ChildElab (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).names
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).context source core type ↔
      ChildElab inputs.names inputs.context source core type := by
  simpa only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context] using covariance

private theorem tail_preimage {original renamed : LocalTypeInputs}
    {owner : Resolved.DeclarationId} {name : String} {type : Core.Ty}
    (same : renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) :
    renamed.bindFresh (mapping owner) name type =
      (original.bindFresh owner name type).mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective) := by
  rw [same]
  exact (LocalTypeInputs.bindFresh_mapOwner original owner mapping injective name type).symm

private theorem elab_reflect
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {renamed : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types (mapping owner) renamed body core type) :
    ∀ original : LocalTypeInputs,
      renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) →
      ComputationReturnTreeElaborates ChildElab types owner original body core type := by
  induction elaboration with
  | bare => intro original same; exact .bare
  | expression child =>
      intro original same
      exact .expression ((child_iff mapping injective covariance).mp (same ▸ child))
  | block _ ih => intro original same; exact .block (ih original same)
  | binding meaning initializer _ ih =>
      intro original same
      exact .binding meaning ((child_iff mapping injective covariance).mp (same ▸ initializer))
        (ih _ (tail_preimage mapping injective same))
  | inferred initializer _ ih =>
      intro original same
      exact .inferred ((child_iff mapping injective covariance).mp (same ▸ initializer))
        (ih _ (tail_preimage mapping injective same))
  | discard child _ ih =>
      intro original same
      exact .discard ((child_iff mapping injective covariance).mp (same ▸ child)) (ih original same)
  | conditional condition protection _ _ thenIH elseIH =>
      intro original same
      refine .conditional ((child_iff mapping injective covariance).mp (same ▸ condition)) ?_
        (thenIH original same) (elseIH original same)
      rw [same] at protection
      simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
        Function.comp_def] using protection
  | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
      intro original same
      exact .wordMatch ((child_iff mapping injective covariance).mp (same ▸ scrutinee))
        ordered patterns compatible (fun entry member => branchIH entry member original same)
        defaultOrdered (fun entry member => defaultIH entry member original same) lowered

/-- All original branches and exact lowering survive in both directions under
the same child's independent covariance, including non-surjective owner maps. -/
theorem computationReturnTreeElaborates_mapOwner_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    ComputationReturnTreeElaborates ChildElab types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body core type ↔
      ComputationReturnTreeElaborates ChildElab types owner inputs body core type := by
  constructor
  · intro elaboration
    exact elab_reflect mapping injective covariance elaboration inputs rfl
  · intro elaboration
    induction elaboration with
    | bare => exact .bare
    | expression child => exact .expression ((child_iff mapping injective covariance).mpr child)
    | block _ ih => exact .block ih
    | binding meaning initializer _ ih =>
        refine .binding meaning ((child_iff mapping injective covariance).mpr initializer) ?_
        simpa only [LocalTypeInputs.bindFresh_mapOwner _ owner mapping injective] using ih
    | inferred initializer _ ih =>
        refine .inferred ((child_iff mapping injective covariance).mpr initializer) ?_
        simpa only [LocalTypeInputs.bindFresh_mapOwner _ owner mapping injective] using ih
    | discard child _ ih => exact .discard ((child_iff mapping injective covariance).mpr child) ih
    | conditional condition protection _ _ thenIH elseIH =>
        refine .conditional ((child_iff mapping injective covariance).mpr condition) ?_ thenIH elseIH
        simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
          Function.comp_def] using protection
    | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
        exact .wordMatch ((child_iff mapping injective covariance).mpr scrutinee)
          ordered patterns compatible branchIH defaultOrdered defaultIH lowered

variable {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}

private theorem type_child_iff
    (covariance : ∀ {table context source type},
      ChildHasType (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source type ↔
        ChildHasType table context source type)
    {inputs : LocalTypeInputs} {source : Syntax.Expr} {type : Core.Ty} :
    ChildHasType (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).names
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).context source type ↔
      ChildHasType inputs.names inputs.context source type := by
  simpa only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context] using covariance

private theorem type_reflect
    (covariance : ∀ {table context source type},
      ChildHasType (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source type ↔
        ChildHasType table context source type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {renamed : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : ComputationReturnTreeHasType ChildHasType types (mapping owner) renamed body type) :
    ∀ original : LocalTypeInputs,
      renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) →
      ComputationReturnTreeHasType ChildHasType types owner original body type := by
  induction typing with
  | bare => intro original same; exact .bare
  | expression child =>
      intro original same
      exact .expression ((type_child_iff mapping injective covariance).mp (same ▸ child))
  | block _ ih => intro original same; exact .block (ih original same)
  | binding meaning initializer _ ih =>
      intro original same
      exact .binding meaning ((type_child_iff mapping injective covariance).mp (same ▸ initializer))
        (ih _ (tail_preimage mapping injective same))
  | inferred initializer _ ih =>
      intro original same
      exact .inferred ((type_child_iff mapping injective covariance).mp (same ▸ initializer))
        (ih _ (tail_preimage mapping injective same))
  | discard child _ ih =>
      intro original same
      exact .discard ((type_child_iff mapping injective covariance).mp (same ▸ child)) (ih original same)
  | conditional condition protection _ _ thenIH elseIH =>
      intro original same
      refine .conditional ((type_child_iff mapping injective covariance).mp (same ▸ condition)) ?_
        (thenIH original same) (elseIH original same)
      rw [same] at protection
      simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
        Function.comp_def] using protection
  | wordMatch scrutinee patterns compatible covered _ _ branchIH defaultIH =>
      intro original same
      exact .wordMatch ((type_child_iff mapping injective covariance).mp (same ▸ scrutinee))
        patterns compatible covered (fun arm member => branchIH arm member original same)
        (fun source member => defaultIH source member original same)

/-- Independent typing transport needs only child typing covariance, not child
elaboration existence, checking or inhabitants for the original input types. -/
theorem computationReturnTreeHasType_mapOwner_iff
    (covariance : ∀ {table context source type},
      ChildHasType (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source type ↔
        ChildHasType table context source type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    ComputationReturnTreeHasType ChildHasType types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body type ↔
      ComputationReturnTreeHasType ChildHasType types owner inputs body type := by
  constructor
  · intro typing
    exact type_reflect mapping injective covariance typing inputs rfl
  · intro typing
    induction typing with
    | bare => exact .bare
    | expression child => exact .expression ((type_child_iff mapping injective covariance).mpr child)
    | block _ ih => exact .block ih
    | binding meaning initializer _ ih =>
        refine .binding meaning ((type_child_iff mapping injective covariance).mpr initializer) ?_
        simpa only [LocalTypeInputs.bindFresh_mapOwner _ owner mapping injective] using ih
    | inferred initializer _ ih =>
        refine .inferred ((type_child_iff mapping injective covariance).mpr initializer) ?_
        simpa only [LocalTypeInputs.bindFresh_mapOwner _ owner mapping injective] using ih
    | discard child _ ih => exact .discard ((type_child_iff mapping injective covariance).mpr child) ih
    | conditional condition protection _ _ thenIH elseIH =>
        refine .conditional ((type_child_iff mapping injective covariance).mpr condition) ?_ thenIH elseIH
        simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
          Function.comp_def] using protection
    | wordMatch scrutinee patterns compatible covered _ _ branchIH defaultIH =>
        exact .wordMatch ((type_child_iff mapping injective covariance).mpr scrutinee)
          patterns compatible covered branchIH defaultIH

/-- The same fixed child operation supplies complete covariance. Its local
success graph is used only to transport the entire optional checker result. -/
theorem elaborateComputationReturnTree?_mapOwner
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (covariance : ∀ table context source,
      checkChild (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source =
        checkChild table context source)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateComputationReturnTree? checkChild types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body =
      elaborateComputationReturnTree? checkChild types owner inputs body := by
  let Graph := fun table context source core type => checkChild table context source = some (core, type)
  have graphCovariance : ∀ {table context source core type},
      Graph (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        Graph table context source core type := by
    intro table context source core type
    dsimp only [Graph]
    rw [covariance]
  have accepted_iff {core type} :
      elaborateComputationReturnTree? checkChild types (mapping owner)
          (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body = some (core, type) ↔
        elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type) :=
    (elaborateComputationReturnTree?_iff (ChildElab := Graph) Iff.rfl).trans
      ((computationReturnTreeElaborates_mapOwner_iff mapping injective graphCovariance).trans
        (elaborateComputationReturnTree?_iff (ChildElab := Graph) Iff.rfl).symm)
  cases original : elaborateComputationReturnTree? checkChild types owner inputs body with
  | none =>
      cases renamed : elaborateComputationReturnTree? checkChild types (mapping owner)
          (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body with
      | none => rfl
      | some result =>
          obtain ⟨core, type⟩ := result
          have impossible := accepted_iff.mp renamed
          rw [original] at impossible
          cases impossible
  | some result =>
      obtain ⟨core, type⟩ := result
      exact accepted_iff.mpr original

end Solcore.Frontend
