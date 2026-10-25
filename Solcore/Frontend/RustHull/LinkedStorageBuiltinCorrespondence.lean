import Solcore.Frontend.RustHull.StorageBuiltinCorrespondence
import Solcore.Frontend.RustHull.RuntimeLinkedWorldCorrespondence

/-! Storage lowering preserves the exact catalog identity attached to each
selected account, including writes and static-write rejection. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedStorageBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence StorageBuiltinCorrespondence

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation with
  | load transient | store transient =>
    cases transient <;>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals first
      | rfl
      | change Except.error _ = Except.ok lowered at compiled
        cases compiled

private theorem load_components (transient : Bool) {scope : Scope} {key : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.load transient).name [key] = .ok lowered) :
    ∃ world address complete,
      Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "address" .word = .ok address ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      lowered = ⟨.word, AccountState.readStorage world (.loadCell address) (.loadCell complete) key transient⟩ := by
  have components : (do
      let raw ← (do
        let world ← Effects.reference scope "world" AccountState.type
        let address ← Effects.reference scope "address" .word
        let complete ← Effects.reference scope "worldComplete" .bool
        pure (Lowered.mk .word (AccountState.readStorage world (.loadCell address) (.loadCell complete) key transient)) : LowerM Lowered)
      pure raw) = .ok lowered := by
    cases transient <;> exact compiled
  obtain ⟨world, worldCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨address, addressCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨complete, completeCompiled, returned⟩ := lower_bind_eq_ok.mp components
  exact ⟨world, address, complete, worldCompiled, addressCompiled, completeCompiled, (Except.ok.inj returned).symm⟩

private theorem store_components (transient : Bool) {scope : Scope} {key value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.store transient).name [key, value] = .ok lowered) :
    ∃ static stop world address complete,
      Effects.reference scope "isStatic" .bool = .ok static ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop ∧
      Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "address" .word = .ok address ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      lowered = ⟨.unit, .ifE (.loadCell static) stop
        (AccountState.writeStorage world (.loadCell address) (.loadCell complete) key value transient)⟩ := by
  have components : (do
      let raw ← (do
        let static ← Effects.reference scope "isStatic" .bool
        let stop ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
        let world ← Effects.reference scope "world" AccountState.type
        let address ← Effects.reference scope "address" .word
        let complete ← Effects.reference scope "worldComplete" .bool
        pure (Lowered.mk .unit (.ifE (.loadCell static) stop
          (AccountState.writeStorage world (.loadCell address) (.loadCell complete) key value transient))) : LowerM Lowered)
      pure raw) = .ok lowered := by
    cases transient <;> exact compiled
  obtain ⟨static, staticCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨stop, stopCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨world, worldCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨address, addressCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨complete, completeCompiled, returned⟩ := lower_bind_eq_ok.mp components
  exact ⟨static, stop, world, address, complete, staticCompiled, stopCompiled, worldCompiled,
    addressCompiled, completeCompiled, (Except.ok.inj returned).symm⟩

theorem load_preserves (transient : Bool)
    {scope : Scope} {keyExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.load transient).name [keyExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (stateRelated : StorageBuiltinCorrespondence.StateRel locations state store)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors state.world locations.world store)
    (key : Word) (keyEvaluated : Evaluates environment store (keyExpr.rename mapping) (.word key) store) :
    ∃ target final,
      ResultRel lowered.type (StorageSemantics.load state key transient).1 target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧
      RuntimeLinkedWorldCorrespondence.StateRel anchors (StorageSemantics.load state key transient).2.world locations.world final := by
  obtain ⟨world, address, complete, worldCompiled, addressCompiled, completeCompiled, rfl⟩ := load_components transient compiled
  obtain ⟨final, evaluated, worldRelated, frame⟩ := RuntimeLinkedWorldCorrespondence.readStorage_preserves state.address state.complete key transient
    (.pair (reference_evaluates runtime worldMember worldCompiled store)
      (.pair (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
        (.pair (.loadCell (reference_evaluates runtime completeMember completeCompiled store) stateRelated.complete) keyEvaluated)))
    linked
  refine ⟨_, final, load_result state key transient, ?_, ?_⟩
  · rw [readStorage_rename]
    exact evaluated
  · rw [load_state]
    exact worldRelated

theorem store_preserves (transient : Bool)
    {scope : Scope} {keyExpr valueExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.store transient).name [keyExpr, valueExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StorageBuiltinCorrespondence.StateRel locations state store)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors state.world locations.world store)
    (key value : Word)
    (keyEvaluated : Evaluates environment store (keyExpr.rename mapping) (.word key) store)
    (valueEvaluated : Evaluates environment store (valueExpr.rename mapping) (.word value) store) :
    ∃ target final,
      ResultRel lowered.type (StorageSemantics.store state key value transient).1 target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧
      RuntimeLinkedWorldCorrespondence.StateRel anchors (StorageSemantics.store state key value transient).2.world locations.world final := by
  obtain ⟨static, stop, world, address, complete, staticCompiled, stopCompiled, worldCompiled,
    addressCompiled, completeCompiled, rfl⟩ := store_components transient compiled
  have staticRead := stateRelated.isStatic
  cases permitted : state.isStatic
  · rw [permitted] at staticRead
    obtain ⟨final, evaluated, worldRelated, frame⟩ := RuntimeLinkedWorldCorrespondence.writeStorage_preserves state.address state.complete key value transient
      (.pair (reference_evaluates runtime worldMember worldCompiled store)
        (.pair (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
          (.pair (.loadCell (reference_evaluates runtime completeMember completeCompiled store) stateRelated.complete)
            (.pair keyEvaluated valueEvaluated)))) linked
    refine ⟨_, final, store_result state key value transient permitted, ?_, ?_⟩
    · apply Evaluates.ifFalse (.loadCell (reference_evaluates runtime staticMember staticCompiled store) staticRead)
      rw [writeStorage_rename]
      exact evaluated
    · rw [store_state state key value transient permitted]
      exact worldRelated
  · rw [permitted] at staticRead
    refine ⟨.inLeft .unit (.word Word.maximum), haltStore locations store, ?_, ?_, ?_⟩
    · simpa only [StorageSemantics.store, permitted, ↓reduceIte] using (ResultRel.language (type := .unit) Word.maximum)
    · apply Evaluates.ifTrue (.loadCell (reference_evaluates runtime staticMember staticCompiled store) staticRead)
      exact stop_evaluates stopCompiled runtime memorySizeMember exitMember offsetMember sizeMember stateRelated
    · simp only [StorageSemantics.store, permitted, ↓reduceIte]
      have distinct := stateRelated.distinct
      simp [Locations.all] at distinct
      exact linked.read_preserved (fun _ found => haltStore_other
        (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) found)


/-- Successful compilation and initialized runtime cells determine each
storage observation, including static rejection and all resulting writes. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StorageBuiltinCorrespondence.StateRel locations state store)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors state.world locations.world store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store)
    (sourceType : Ty) :
    ∃ result finalState target finalStore,
      StorageSemantics.builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      RuntimeLinkedWorldCorrespondence.StateRel anchors finalState.world locations.world finalStore := by
  have supported : Effects.supports operation.name = true := by
    cases operation with | load transient | store transient => cases transient <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  cases operation with
  | load transient =>
      obtain ⟨keyExpr, key, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨target, final, resultRelated, evaluated, finalRelated⟩ := load_preserves transient rawCompiled
        (runtime.temporary .word (.word key)) worldMember addressMember completeMember stateRelated linked key (.var rfl)
      cases typed
      cases loweredEqual
      refine ⟨(StorageSemantics.load state key transient).1, (StorageSemantics.load state key transient).2,
        target, final, ?_, resultRelated, ?_, finalRelated⟩
      · cases transient <;> rfl
      · exact LanguageResult.bind_success _ packed evaluated
  | store transient =>
      obtain ⟨keyExpr, valueExpr, key, value, rfl, rfl, rfl⟩ := two_words related words arity
      obtain ⟨target, final, resultRelated, evaluated, finalRelated⟩ := store_preserves transient rawCompiled
        (runtime.temporary (.product .word .word) (.pair (.word key) (.word value)))
        worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
        stateRelated linked key value (.first (.var rfl)) (.second (.var rfl))
      cases typed
      cases loweredEqual
      refine ⟨(StorageSemantics.store state key value transient).1, (StorageSemantics.store state key value transient).2,
        target, final, ?_, resultRelated, ?_, finalRelated⟩
      · cases transient <;> rfl
      · exact LanguageResult.bind_success _ packed evaluated

end Solcore.Frontend.RustHull.LinkedStorageBuiltinCorrespondence
