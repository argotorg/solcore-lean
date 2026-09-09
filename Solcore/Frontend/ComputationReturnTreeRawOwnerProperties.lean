import Solcore.Frontend.ComputationReturnTreeEvaluation
import Solcore.Frontend.LocalNameRenaming
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Resolved.Renaming

/-! Owner-only relabeling preserves shared raw evidence and exact costs.
The two child relations have independent covariance premises. Reflection keeps
both original raw tables; neither alignment nor runtime typing is required. -/

set_option autoImplicit false
namespace Solcore.Frontend

variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
include injective

private theorem fresh_mapOwner (owner : Resolved.DeclarationId) (table : LocalNameTable) :
    Resolved.freshLocalId (mapping owner)
        ((LocalNameTable.mapIds (ownerLocalIdMap mapping) table).map Prod.snd) =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner (table.map Prod.snd)) := by
  simpa only [LocalNameTable.mapIds, List.map_map, Function.comp_def, ownerLocalIdMap,
    Resolved.freshLocalId_owner] using
    Resolved.freshLocalId_map_owner mapping injective owner (table.map Prod.snd)

variable {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}

private theorem eval_reflect
    (covariance : ∀ {table environment initialStore source value finalStore},
      ChildEval (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore source value finalStore ↔
        ChildEval table environment initialStore source value finalStore)
    {owner : Resolved.DeclarationId} {renamedTable : LocalNameTable}
    {renamedEnvironment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value}
    (evaluation : ComputationReturnTreeEvaluates ChildEval (mapping owner)
      renamedTable renamedEnvironment initialStore body value finalStore) :
    ∀ (table : LocalNameTable) (environment : Resolved.Environment),
      renamedTable = LocalNameTable.mapIds (ownerLocalIdMap mapping) table →
      renamedEnvironment = Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment →
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore body value finalStore := by
  induction evaluation with
  | bare => intro table environment tableSame environmentSame; exact .bare
  | expression child =>
      intro table environment tableSame environmentSame
      exact .expression (covariance.mp (tableSame ▸ environmentSame ▸ child))
  | block _ ih =>
      intro table environment tableSame environmentSame
      exact .block (ih table environment tableSame environmentSame)
  | binding initializer _ ih =>
      intro table environment tableSame environmentSame
      refine .binding (covariance.mp (tableSame ▸ environmentSame ▸ initializer)) (ih _ _ ?_ ?_)
      · rw [tableSame, fresh_mapOwner mapping injective]; rfl
      · rw [tableSame, environmentSame, fresh_mapOwner mapping injective]; rfl
  | inferred initializer _ ih =>
      intro table environment tableSame environmentSame
      refine .inferred (covariance.mp (tableSame ▸ environmentSame ▸ initializer)) (ih _ _ ?_ ?_)
      · rw [tableSame, fresh_mapOwner mapping injective]; rfl
      · rw [tableSame, environmentSame, fresh_mapOwner mapping injective]; rfl
  | discard child _ ih =>
      intro table environment tableSame environmentSame
      exact .discard (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | ifTrue child _ ih =>
      intro table environment tableSame environmentSame
      exact .ifTrue (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | ifFalse child _ ih =>
      intro table environment tableSame environmentSame
      exact .ifFalse (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | wordMatch child choice _ ih =>
      intro table environment tableSame environmentSame
      exact .wordMatch (covariance.mp (tableSame ▸ environmentSame ▸ child)) choice
        (ih table environment tableSame environmentSame)

/-- The same child's raw covariance preserves and reflects the original body
on arbitrary ordered rows, including duplicates and environment-only IDs. -/
theorem computationReturnTreeEvaluates_mapOwner_iff
    (covariance : ∀ {table environment initialStore source value finalStore},
      ChildEval (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore source value finalStore ↔
        ChildEval table environment initialStore source value finalStore)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    ComputationReturnTreeEvaluates ChildEval (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore body value finalStore ↔
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore body value finalStore := by
  constructor
  · intro evaluation
    exact eval_reflect mapping injective covariance evaluation table environment rfl rfl
  · intro evaluation
    induction evaluation with
    | bare => exact .bare
    | expression child => exact .expression (covariance.mpr child)
    | block _ ih => exact .block ih
    | binding initializer _ ih =>
        refine .binding (covariance.mpr initializer) ?_
        rw [fresh_mapOwner mapping injective]
        exact ih
    | inferred initializer _ ih =>
        refine .inferred (covariance.mpr initializer) ?_
        rw [fresh_mapOwner mapping injective]
        exact ih
    | discard child _ ih => exact .discard (covariance.mpr child) ih
    | ifTrue child _ ih => exact .ifTrue (covariance.mpr child) ih
    | ifFalse child _ ih => exact .ifFalse (covariance.mpr child) ih
    | wordMatch child choice _ ih => exact .wordMatch (covariance.mpr child) choice ih

variable {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}

private theorem cost_reflect
    (covariance : ∀ {table environment initialStore source value finalStore cost},
      ChildCost (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore source value finalStore cost ↔
        ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {renamedTable : LocalNameTable}
    {renamedEnvironment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ComputationReturnTreeEvaluatesWithCost ChildCost (mapping owner)
      renamedTable renamedEnvironment initialStore body value finalStore cost) :
    ∀ (table : LocalNameTable) (environment : Resolved.Environment),
      renamedTable = LocalNameTable.mapIds (ownerLocalIdMap mapping) table →
      renamedEnvironment = Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment →
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | bare => intro table environment tableSame environmentSame; exact .bare
  | expression child =>
      intro table environment tableSame environmentSame
      exact .expression (covariance.mp (tableSame ▸ environmentSame ▸ child))
  | block _ ih =>
      intro table environment tableSame environmentSame
      exact .block (ih table environment tableSame environmentSame)
  | binding initializer _ ih =>
      intro table environment tableSame environmentSame
      refine .binding (covariance.mp (tableSame ▸ environmentSame ▸ initializer)) (ih _ _ ?_ ?_)
      · rw [tableSame, fresh_mapOwner mapping injective]; rfl
      · rw [tableSame, environmentSame, fresh_mapOwner mapping injective]; rfl
  | inferred initializer _ ih =>
      intro table environment tableSame environmentSame
      refine .inferred (covariance.mp (tableSame ▸ environmentSame ▸ initializer)) (ih _ _ ?_ ?_)
      · rw [tableSame, fresh_mapOwner mapping injective]; rfl
      · rw [tableSame, environmentSame, fresh_mapOwner mapping injective]; rfl
  | discard child _ ih =>
      intro table environment tableSame environmentSame
      exact .discard (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | ifTrue child _ ih =>
      intro table environment tableSame environmentSame
      exact .ifTrue (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | ifFalse child _ ih =>
      intro table environment tableSame environmentSame
      exact .ifFalse (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | wordMatch child choice _ ih =>
      intro table environment tableSame environmentSame
      exact .wordMatch (covariance.mp (tableSame ▸ environmentSame ▸ child)) choice
        (ih table environment tableSame environmentSame)

/-- The same child's exact-cost covariance preserves all stores, selected
branches and costs independently of any uncosted/cost-existence bridge. -/
theorem computationReturnTreeEvaluatesWithCost_mapOwner_iff
    (covariance : ∀ {table environment initialStore source value finalStore cost},
      ChildCost (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore source value finalStore cost ↔
        ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    ComputationReturnTreeEvaluatesWithCost ChildCost (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore body value finalStore cost ↔
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore body value finalStore cost := by
  constructor
  · intro evaluation
    exact cost_reflect mapping injective covariance evaluation table environment rfl rfl
  · intro evaluation
    induction evaluation with
    | bare => exact .bare
    | expression child => exact .expression (covariance.mpr child)
    | block _ ih => exact .block ih
    | binding initializer _ ih =>
        refine .binding (covariance.mpr initializer) ?_
        rw [fresh_mapOwner mapping injective]
        exact ih
    | inferred initializer _ ih =>
        refine .inferred (covariance.mpr initializer) ?_
        rw [fresh_mapOwner mapping injective]
        exact ih
    | discard child _ ih => exact .discard (covariance.mpr child) ih
    | ifTrue child _ ih => exact .ifTrue (covariance.mpr child) ih
    | ifFalse child _ ih => exact .ifFalse (covariance.mpr child) ih
    | wordMatch child choice _ ih => exact .wordMatch (covariance.mpr child) choice ih

end Solcore.Frontend
