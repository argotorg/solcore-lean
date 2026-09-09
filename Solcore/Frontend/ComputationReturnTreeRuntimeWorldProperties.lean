import Solcore.Frontend.ComputationReturnTreeRuntimeCheckpointProperties

/-! Actual saved stores have uniquely determined worlds extending the supplied
world. Every further finite path retains a further extension of that same world. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem world_types {world : Core.StoreTyping} {store : Core.Store}
    (typed : Core.StoreHasTypes world store) : world = store.map Core.Value.type := by
  induction world generalizing store with
  | nil =>
      have empty : store = [] := List.length_eq_zero_iff.mp typed.length_eq.symm
      subst store; rfl
  | cons type types ih =>
      cases store with
      | nil => have impossible := typed.length_eq; cases impossible
      | cons value values =>
          obtain ⟨head,found,_,headTyped⟩ := typed.lookup (location := 0) rfl
          have same : head = value := (Option.some.inj found).symm
          subst head
          have tail : Core.StoreHasTypes types values :=
            ⟨Nat.succ.inj typed.length_eq,fun {index _} found => typed.lookup (location := index+1) found⟩
          simp only [List.map_cons,← headTyped.type_eq,ih tail]

private theorem world_unique {left right : Core.StoreTyping} {store : Core.Store}
    (first : Core.StoreHasTypes left store) (second : Core.StoreHasTypes right store) : left = right :=
  (world_types first).trans (world_types second).symm

private theorem transition_world {definitions : Core.DataEnvironment} {state next : Core.State}
    {resultType : Core.Ty} {world : Core.StoreTyping}
    (typed : Core.StateHasType state resultType definitions) (stored : Core.StoreHasTypes world state.store)
    (transition : Core.Transition state next) :
    ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future next.store := by
  cases transition <;> try exact ⟨world,Core.WorldExtends.refl world,stored⟩
  case applyNewCell =>
    cases typed with
    | @ret _ actualWorld _ _ _ _ _ actualStored valueTyped continuationTyped =>
        have same : actualWorld = world := world_unique actualStored stored
        subst actualWorld
        cases continuationTyped with
        | cons frame _ => cases frame with
          | newCellApply payload =>
              exact ⟨_,⟨[_],rfl⟩,stored.allocate payload (payload.valueHasType_rebase valueTyped.erase)⟩
  case applyStoreCell =>
    rename_i written
    cases typed with
    | @ret _ actualWorld _ _ _ _ _ actualStored valueTyped continuationTyped =>
        have same : actualWorld = world := world_unique actualStored stored
        subst actualWorld
        cases continuationTyped with
        | cons frame _ => cases frame with
          | storeCellApply found payload =>
              exact ⟨world,Core.WorldExtends.refl world,
                stored.write found (payload.valueHasType_rebase valueTyped.erase) written⟩

private theorem steps_world {definitions : Core.DataEnvironment} {start finish : Core.State}
    {resultType : Core.Ty} {world : Core.StoreTyping} {steps : Nat}
    (typed : Core.StateHasType start resultType definitions) (stored : Core.StoreHasTypes world start.store)
    (path : Core.Steps steps start finish) :
    ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future finish.store := by
  induction path generalizing world with
  | refl => exact ⟨world,Core.WorldExtends.refl world,stored⟩
  | cons transition tail ih =>
      obtain ⟨middle,extended,middleStored⟩ := transition_world typed stored transition
      obtain ⟨future,further,finalStored⟩ := ih (Core.transition_preserves_state_type typed transition) middleStored
      exact ⟨future,extended.trans further,finalStored⟩

theorem ComputationReturnTreeElaborates.runtime_checkpoint_world_extension
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    {world : Core.StoreTyping} {environment : Core.Environment} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment inputs.context.values)
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType)
    {spent : Nat} {checkpoint : Core.State}
    (exhausted : Core.runStateful spent ⟨.eval core environment,continuation,store⟩ = .outOfFuel checkpoint) :
    ∃ savedWorld, Core.WorldExtends world savedWorld ∧ Core.StoreHasTypes savedWorld checkpoint.store ∧
      ∀ {steps next}, Core.Steps steps checkpoint next →
        ∃ future, Core.WorldExtends savedWorld future ∧ Core.StoreHasTypes future next.store := by
  have safe := elaboration.runtime_checkpoint_safety childCoreType environmentTyped storeTyped continuationTyped
  have path := (Core.runStateful_outOfFuel_sound exhausted).1
  obtain ⟨savedWorld,extended,savedStored⟩ := steps_world safe.1 storeTyped path
  exact ⟨savedWorld,extended,savedStored,fun further => steps_world (safe.2.2 exhausted).1 savedStored further⟩

end Solcore.Frontend
