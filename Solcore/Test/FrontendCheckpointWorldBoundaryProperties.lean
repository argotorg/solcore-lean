import Solcore.Frontend.Computation

/-! A genuine checkpoint is essential, and independently typed endpoint stores
do not compensate for an untyped pending write. No source-ID law is needed. -/
set_option autoImplicit false
namespace Tests.FrontendCheckpointWorldBoundary
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"WorldBoundary",by decide⟩],by decide⟩⟩,93⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-world-boundary.sol"⟩,0,7⟩
private def body : Syntax.Block := ⟨span,[⟨span,.returnStmt none⟩]⟩
private def child (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) (_ : Core.Expr) (_ : Core.Ty) : Prop := False
private theorem childType {names context source core type} (h : child names context source core type) :
    Core.HasType context.values core type := False.elim h
private theorem elaboration :
    ComputationReturnTreeElaborates child [] owner .empty body .unit .unit := .bare
private def pending : List Core.Frame := [.newCellApply .unit,.loadCellApply]
private def started (store : Core.Store) : Core.State := ⟨.eval .unit [],pending,store⟩
private def saved (store : Core.Store) : Core.State := ⟨.ret .unit,pending,store⟩
private def allocated (store : Core.Store) : Core.State :=
  ⟨.ret (.cellRef .unit store.length),[.loadCellApply],store++[.unit]⟩
private theorem pendingTyped (world : Core.StoreTyping) : Core.ContinuationHasType world pending .unit .unit :=
  .cons .newCellApply (.cons .loadCellApply .nil)
private theorem stopped (store : Core.Store) : Core.runStateful 1 (started store) = .outOfFuel (saved store) := rfl
private theorem allocatedPath (store : Core.Store) : Core.Steps 1 (saved store) (allocated store) :=
  .cons .applyNewCell .refl

theorem original_bare_body_has_an_actual_pending_allocation_checkpoint (store : Core.Store) :
    ComputationReturnTreeElaborates child [] owner .empty body .unit .unit ∧
    Core.Steps 1 (started store) (saved store) ∧
    Core.runStateful 1 (started store) = .outOfFuel (saved store) ∧
    Core.runStateful 1 (saved store) = .outOfFuel (allocated store) := by
  refine ⟨elaboration,.cons .unit .refl,stopped store,?_⟩
  exact Core.runStateful_outOfFuel_complete (allocatedPath store)
    (Core.advance_next_iff.mpr (.applyLoadCell (Core.Store.allocate_fresh_lookup store .unit)))

theorem extending_worlds_retain_every_old_reference_across_actual_resume_paths
    (world : Core.StoreTyping) (store : Core.Store) (typed : Core.StoreHasTypes world store) :
    ∃ checkpointWorld, Core.WorldExtends world checkpointWorld ∧
      Core.RuntimeStoreHasTypes checkpointWorld (saved store).store ∧
      ∀ {steps next}, Core.Steps steps (saved store) next →
        ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future next.store ∧
          ∀ {location : Nat} {type : Core.Ty}, world[location]? = some type → future[location]? = some type := by
  obtain ⟨checkpointWorld,extension,stored,further⟩ :=
    elaboration.runtime_checkpoint_world_extension childType
      (world := world) (environment := []) (store := store)
      Core.RuntimeEnvironmentHasTypes.nil typed (pendingTyped world) (stopped store)
  refine ⟨checkpointWorld,extension,stored,?_⟩
  intro steps next path
  obtain ⟨future,more,stored⟩ := further path
  exact ⟨future,extension.trans more,stored,fun found => (extension.trans more).lookup found⟩

theorem allocation_grows_the_world_without_changing_old_cell_types
    (world : Core.StoreTyping) (store : Core.Store) (typed : Core.StoreHasTypes world store) :
    ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future (store++[.unit]) ∧
      world.length < future.length ∧
      ∀ {location : Nat} {type : Core.Ty}, world[location]? = some type → future[location]? = some type := by
  obtain ⟨_,_,_,further⟩ := extending_worlds_retain_every_old_reference_across_actual_resume_paths world store typed
  obtain ⟨future,extension,stored,retained⟩ := further (allocatedPath store)
  refine ⟨future,extension,stored,?_,retained⟩
  have lengths := stored.length_eq
  have original := typed.length_eq
  change future.length = (store++[Core.Value.unit]).length at lengths
  simp only [List.length_append,List.length_singleton] at lengths
  omega

theorem old_checkpoint_safety_and_new_world_extension_apply_to_the_same_saved_state
    (world : Core.StoreTyping) (store : Core.Store) (typed : Core.StoreHasTypes world store) :
    Core.StateHasType (saved store) .unit ∧
      (∀ fuel error faultState, Core.runStateful fuel (saved store) ≠ .fault error faultState) ∧
      ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future (saved store).store := by
  have old := elaboration.runtime_checkpoint_safety childType
    (world := world) (environment := []) (store := store)
    Core.RuntimeEnvironmentHasTypes.nil typed (pendingTyped world)
  obtain ⟨future,extension,stored,_⟩ :=
    elaboration.runtime_checkpoint_world_extension childType
      (world := world) (environment := []) (store := store)
      Core.RuntimeEnvironmentHasTypes.nil typed (pendingTyped world) (stopped store)
  exact ⟨(old.2.2 (stopped store)).1,(old.2.2 (stopped store)).2,future,extension,stored⟩

private def badStart (word : Core.Word) : Core.State :=
  ⟨.eval .unit [],[.storeCellApply .word 0],[.word word]⟩
private def badSaved (word : Core.Word) : Core.State :=
  ⟨.ret .unit,[.storeCellApply .word 0],[.word word]⟩
private def badFinal : Core.State := ⟨.ret .unit,[],[.unit]⟩
private def foreignSaved : Core.State := ⟨.ret .unit,[.newCellApply .unit],[.unit]⟩
private theorem noExtension : ¬ Core.WorldExtends [.word] [.unit] := by
  intro extension
  have found := extension.lookup (location := 0) (type := .word) rfl
  cases found

theorem separately_typed_equal_length_stores_do_not_supply_a_world_extension
    (word : Core.Word) :
    ComputationReturnTreeElaborates child [] owner .empty body .unit .unit ∧
    Core.StoreHasTypes [.word] [.word word] ∧ Core.StoreHasTypes [.unit] [.unit] ∧
    Core.Steps 2 (badStart word) badFinal ∧
    Core.runStateful 1 (badStart word) = .outOfFuel (badSaved word) ∧
    Core.runStateful 1 (badSaved word) = .done .unit [.unit] ∧
    ([.word] : Core.StoreTyping).length = ([.unit] : Core.StoreTyping).length ∧
    ¬ Core.WorldExtends [.word] [.unit] :=
  ⟨elaboration,Core.StoreHasTypes.nil.allocate .word .word,
    Core.StoreHasTypes.nil.allocate .unit .unit,
    .cons .unit (.cons (.applyStoreCell rfl) .refl),rfl,rfl,rfl,noExtension⟩

theorem a_typed_source_and_store_cannot_replace_the_pending_frame_premise
    (word : Core.Word) :
    Core.HasType [] .unit .unit ∧ Core.RuntimeEnvironmentHasTypes [.word] [] [] ∧
    Core.StoreHasTypes [.word] (badStart word).store ∧
    (¬ ∃ result, Core.ContinuationHasType [.word] [.storeCellApply .word 0] .unit result) ∧
    (¬ ∃ result, Core.StateHasType (badStart word) result) := by
  refine ⟨.unit,.nil,Core.StoreHasTypes.nil.allocate .word .word,?_,?_⟩
  · rintro ⟨result,typed⟩
    cases typed with | cons frame _ => cases frame
  · rintro ⟨result,typed⟩
    cases typed with | eval _ _ unitTyped continuation =>
      cases unitTyped
      cases continuation with | cons frame _ => cases frame

theorem no_alternative_world_can_hide_the_changed_type_of_the_original_cell :
    ∀ world, Core.RuntimeStoreHasTypes world [.unit] → ¬ Core.WorldExtends [.word] world := by
  intro world typed extension
  obtain ⟨value,found,valueTyped⟩ := typed.lookup (extension.lookup (location := 0) (type := .word) rfl)
  change some Core.Value.unit = some value at found
  cases found
  cases valueTyped

theorem an_unrelated_typed_state_is_not_a_genuine_checkpoint (word : Core.Word) :
    Core.StateHasType foreignSaved (.cell .unit) ∧
    Core.runStateful 0 foreignSaved = .outOfFuel foreignSaved ∧
    (∀ fuel, Core.runStateful fuel (started [.word word]) ≠ .outOfFuel foreignSaved) := by
  refine ⟨.ret ((Core.StoreHasTypes.nil.allocate .unit .unit).toRuntime) .unit (.cons .newCellApply .nil),rfl,?_⟩
  intro fuel exhausted
  obtain ⟨future,extension,typed,_⟩ :=
    elaboration.runtime_checkpoint_world_extension childType
      (world := [.word]) (environment := []) (store := [.word word])
      Core.RuntimeEnvironmentHasTypes.nil (Core.StoreHasTypes.nil.allocate .word .word)
      (pendingTyped [.word]) exhausted
  exact no_alternative_world_can_hide_the_changed_type_of_the_original_cell future typed extension

end Tests.FrontendCheckpointWorldBoundary
