import Solcore.Frontend.RustHull.StorageCorrespondence
import Solcore.Frontend.RustHull.MemoryCorrespondence
import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport

/-! Concrete storage effects through successful Hull builtin lowering,
including the runtime registers written by rejected static writes. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StorageBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

inductive Operation where
  | load (transient : Bool) | store (transient : Bool)
  deriving DecidableEq

def Operation.name : Operation → String
  | .load false => "sload" | .load true => "tload"
  | .store false => "sstore" | .store true => "tstore"

def Operation.arity : Operation → Nat
  | .load _ => 1 | .store _ => 2

structure Locations where
  world : Nat
  address : Nat
  complete : Nat
  isStatic : Nat
  exit : Nat
  returnOffset : Nat
  returnSize : Nat
  memorySize : Nat

def Locations.all (locations : Locations) : List Nat :=
  [locations.world, locations.address, locations.complete, locations.isStatic,
    locations.exit, locations.returnOffset, locations.returnSize, locations.memorySize]

def Locations.mutable (locations : Locations) : List Nat :=
  [locations.world, locations.exit, locations.returnOffset, locations.returnSize]

structure StateRel (locations : Locations) (state : StorageSemantics.State) (store : Store) : Prop where
  world : StorageCorrespondence.StateRel state.world locations.world store
  address : store.read? locations.address = some (.word state.address)
  complete : store.read? locations.complete = some (.bool state.complete)
  isStatic : store.read? locations.isStatic = some (.bool state.isStatic)
  exit : store.read? locations.exit = some (.word state.exit)
  returnOffset : store.read? locations.returnOffset = some (.word state.returnOffset)
  returnSize : store.read? locations.returnSize = some (.word state.returnSize)
  distinct : locations.all.Nodup

structure Frame (locations : Locations) (initial final : Store) : Prop where
  length_le : initial.length ≤ final.length
  preserved : ∀ location value, location ∉ locations.mutable →
    initial.read? location = some value → final.read? location = some value

theorem Frame.refl (locations : Locations) (store : Store) : Frame locations store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem Frame.of_storage {locations : Locations} {initial final : Store}
    (frame : StorageCorrespondence.Frame locations.world initial final) : Frame locations initial final :=
  ⟨frame.length_le, fun location value outside found => frame.preserved location value
    (fun same => outside (by simp [Locations.mutable, same])) found⟩

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

set_option linter.unusedSimpArgs false in
theorem readStorage_rename (world address complete key : Core.Expr) (transient : Bool) (mapping : Renaming) :
    (AccountState.readStorage world address complete key transient).rename mapping =
      AccountState.readStorage (world.rename mapping) (address.rename mapping) (complete.rename mapping) (key.rename mapping) transient := by
  simp only [AccountState.readStorage, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  cases transient <;>
    simp only [CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load, CodeBuilder.lookup, projectArgument,
      AccountState.get, AccountState.lookup, AccountState.defaultRecord, bundle,
      LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
      OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
      OrderedMapping.runHelper, WordMapping.lookup, WordMapping.lookupBody, WordMapping.runHelper,
      WordMapping.invoke, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
      Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl

set_option linter.unusedSimpArgs false in
theorem writeStorage_rename (world address complete key value : Core.Expr) (transient : Bool) (mapping : Renaming) :
    (AccountState.writeStorage world address complete key value transient).rename mapping =
      AccountState.writeStorage (world.rename mapping) (address.rename mapping) (complete.rename mapping)
        (key.rename mapping) (value.rename mapping) transient := by
  simp only [AccountState.writeStorage, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  cases transient <;>
    simp only [CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load, CodeBuilder.insert, CodeBuilder.success,
      CodeBuilder.store, projectArgument, AccountState.get, AccountState.lookup, AccountState.put,
      AccountState.replace, AccountState.field, AccountState.defaultRecord, bundle,
      LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
      OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.insert, OrderedMapping.insertBody,
      OrderedMapping.cons, OrderedMapping.empty, OrderedMapping.invoke,
      OrderedMapping.runHelper, WordMapping.insert, WordMapping.insertBody, WordMapping.runHelper,
      WordMapping.invoke, WordMapping.cons, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
      Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl


private theorem other_world {locations : Locations} (distinct : locations.all.Nodup) {location : Nat}
    (member : location ∈ [locations.address, locations.complete, locations.isStatic,
      locations.exit, locations.returnOffset, locations.returnSize, locations.memorySize]) : location ≠ locations.world := by
  intro same
  exact (List.nodup_cons.mp distinct).1 (same ▸ member)

theorem StateRel.withWorld {locations : Locations} {state : StorageSemantics.State}
    {initial final : Store} (related : StateRel locations state initial)
    {next : StorageSemantics.World} (world : StorageCorrespondence.StateRel next locations.world final)
    (frame : StorageCorrespondence.Frame locations.world initial final) :
    StateRel locations {state with world := next} final where
  world := world
  address := frame.preserved _ _ (other_world related.distinct (by simp)) related.address
  complete := frame.preserved _ _ (other_world related.distinct (by simp)) related.complete
  isStatic := frame.preserved _ _ (other_world related.distinct (by simp)) related.isStatic
  exit := frame.preserved _ _ (other_world related.distinct (by simp)) related.exit
  returnOffset := frame.preserved _ _ (other_world related.distinct (by simp)) related.returnOffset
  returnSize := frame.preserved _ _ (other_world related.distinct (by simp)) related.returnSize
  distinct := related.distinct

theorem load_result (state : StorageSemantics.State) (key : Word) (transient : Bool) :
    ResultRel .word (StorageSemantics.load state key transient).1
      (StorageCorrespondence.wordResult (StorageSemantics.readStorage state.world state.address state.complete key transient)) := by
  unfold StorageSemantics.load
  cases StorageSemantics.readStorage state.world state.address state.complete key transient with
  | ok value => exact .value (.word _)
  | error reason => exact .language _

theorem store_result (state : StorageSemantics.State) (key value : Word) (transient : Bool)
    (permitted : state.isStatic = false) :
    ResultRel .unit (StorageSemantics.store state key value transient).1
      (StorageCorrespondence.unitResult (StorageSemantics.writeStorage state.world state.address state.complete key value transient)) := by
  simp only [StorageSemantics.store, permitted, Bool.false_eq_true, ↓reduceIte]
  cases StorageSemantics.writeStorage state.world state.address state.complete key value transient with
  | ok next => exact .value .unit
  | error reason => exact .language _

theorem load_state (state : StorageSemantics.State) (key : Word) (transient : Bool) :
    (StorageSemantics.load state key transient).2 = state := by
  unfold StorageSemantics.load
  cases StorageSemantics.readStorage state.world state.address state.complete key transient <;> rfl

theorem store_state (state : StorageSemantics.State) (key value : Word) (transient : Bool)
    (permitted : state.isStatic = false) :
    (StorageSemantics.store state key value transient).2 =
      {state with world := (StorageSemantics.writeStorage state.world state.address state.complete key value transient).toOption.getD state.world} := by
  simp only [StorageSemantics.store, permitted, Bool.false_eq_true, ↓reduceIte]
  cases StorageSemantics.writeStorage state.world state.address state.complete key value transient <;>
    cases state <;> simp_all [Except.toOption]

theorem load_preserves (transient : Bool)
    {scope : Scope} {keyExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.load transient).name [keyExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (stateRelated : StateRel locations state store)
    (key : Word) (keyEvaluated : Evaluates environment store (keyExpr.rename mapping) (.word key) store) :
    ∃ target final,
      ResultRel lowered.type (StorageSemantics.load state key transient).1 target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧
      StateRel locations (StorageSemantics.load state key transient).2 final ∧ Frame locations store final := by
  obtain ⟨world, address, complete, worldCompiled, addressCompiled, completeCompiled, rfl⟩ := load_components transient compiled
  obtain ⟨final, evaluated, worldRelated, frame⟩ := StorageCorrespondence.readStorage_preserves state.address state.complete key transient
    (.pair (reference_evaluates runtime worldMember worldCompiled store)
      (.pair (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
        (.pair (.loadCell (reference_evaluates runtime completeMember completeCompiled store) stateRelated.complete) keyEvaluated)))
    stateRelated.world
  refine ⟨_, final, load_result state key transient, ?_, ?_, Frame.of_storage frame⟩
  · rw [readStorage_rename]
    exact evaluated
  · rw [load_state]
    exact stateRelated.withWorld worldRelated frame


def offsetStore (locations : Locations) (store : Store) : Store :=
  store.set locations.returnOffset (.word Word.zero)

def sizeStore (locations : Locations) (store : Store) : Store :=
  (offsetStore locations store).set locations.returnSize (.word Word.zero)

def haltStore (locations : Locations) (store : Store) : Store :=
  (sizeStore locations store).set
    locations.exit (.word (Word.ofNatModulo 3))

theorem haltStore_other {locations : Locations} {store : Store} {location : Nat} {value : Core.Value}
    (exit : location ≠ locations.exit) (offset : location ≠ locations.returnOffset) (size : location ≠ locations.returnSize)
    (found : store.read? location = some value) :
    (haltStore locations store).read? location = some value := by
  simp only [haltStore, sizeStore, offsetStore, Store.read?, List.getElem?_set_ne (Ne.symm exit),
    List.getElem?_set_ne (Ne.symm offset), List.getElem?_set_ne (Ne.symm size)]
  exact found

theorem haltStore_frame (locations : Locations) (store : Store) : Frame locations store (haltStore locations store) := by
  constructor
  · simp [haltStore, sizeStore, offsetStore]
  · intro location value outside found
    simp [Locations.mutable] at outside
    exact haltStore_other outside.2.1 outside.2.2.1 outside.2.2.2 found

theorem StateRel.halt {locations : Locations} {state : StorageSemantics.State} {store : Store}
    (related : StateRel locations state store) :
    StateRel locations {state with exit := Word.ofNatModulo 3, returnOffset := Word.zero, returnSize := Word.zero}
      (haltStore locations store) := by
  have distinct := related.distinct
  simp [Locations.all] at distinct
  have offsetBound := (List.getElem?_eq_some_iff.mp related.returnOffset).1
  have sizeBound := (List.getElem?_eq_some_iff.mp related.returnSize).1
  have exitBound := (List.getElem?_eq_some_iff.mp related.exit).1
  constructor
  · obtain ⟨accounts, source, found⟩ := related.world
    exact ⟨accounts, source, haltStore_other (locations := locations) (location := locations.world) (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) found⟩
  · exact haltStore_other (locations := locations) (location := locations.address) (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.address
  · exact haltStore_other (locations := locations) (location := locations.complete) (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.complete
  · exact haltStore_other (locations := locations) (location := locations.isStatic) (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.isStatic
  · simp [haltStore, sizeStore, offsetStore, Store.read?, exitBound]
  · simp only [haltStore, sizeStore, offsetStore, Store.read?, List.getElem?_set_ne (by intro same; simp_all : locations.exit ≠ locations.returnOffset),
      List.getElem?_set_ne (by intro same; simp_all : locations.returnSize ≠ locations.returnOffset)]
    simp [offsetBound]
  · simp only [haltStore, sizeStore, offsetStore, Store.read?, List.getElem?_set_ne (by intro same; simp_all : locations.exit ≠ locations.returnSize)]
    simp [sizeBound]
  · exact related.distinct

private theorem reference_position {slots : List EffectSlot} {scope : Scope} {mapping : Renaming}
    {environment : Environment} {slot : EffectSlot} {reference : Core.Expr}
    (related : EffectEnvironmentRel slots scope mapping environment) (member : slot ∈ slots)
    (compiled : Effects.reference scope slot.name slot.type = .ok reference) :
    ∃ index, reference = .var index ∧ environment[mapping index]? = some (.cellRef slot.type slot.location) := by
  unfold Effects.reference at compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  cases returned
  exact ⟨index, rfl, related slot member binding index looked⟩

private theorem stop_components {scope : Scope} {stop : Core.Expr}
    (compiled : Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop) :
    ∃ memorySize exit offset size,
      Effects.reference scope "memorySize" .word = .ok memorySize ∧
      Effects.reference scope "exit" .word = .ok exit ∧
      Effects.reference scope "returnOffset" .word = .ok offset ∧
      Effects.reference scope "returnSize" .word = .ok size ∧
      stop = LocalSequence.discard .unit (Memory.touch memorySize (.word Word.zero) (.word Word.zero))
        ([Core.Expr.storeCell offset (.word Word.zero), .storeCell size (.word Word.zero),
          .storeCell exit (.word (Word.ofNatModulo 3))].foldr (fun store next => .letE store (next.weakenAt 0))
          (LanguageResult.failure .unit (.word Word.maximum))) := by
  unfold Effects.terminate at compiled
  obtain ⟨memorySize, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨exit, exitCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨offset, offsetCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memorySize, exit, offset, size, memoryCompiled, exitCompiled, offsetCompiled, sizeCompiled,
    (Except.ok.inj returned).symm⟩

def haltCells (exit offset size : Nat) (store : Store) : Store :=
  ((store.set offset (.word Word.zero)).set size (.word Word.zero)).set exit (.word (Word.ofNatModulo 3))

/-- Zero-length termination reads no memory-size value. Its execution needs
only the three destination cells and their pairwise separation. -/
theorem stop_evaluates_cells {scope : Scope} {stop : Core.Expr}
    (compiled : Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {memorySizeLocation exitLocation offsetLocation sizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memorySizeMember : ⟨"memorySize", .word, memorySizeLocation⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, exitLocation⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, offsetLocation⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, sizeLocation⟩ ∈ slots)
    {exitValue offsetValue sizeValue : Word}
    (exitInitial : store.read? exitLocation = some (.word exitValue))
    (offsetRead : store.read? offsetLocation = some (.word offsetValue))
    (sizeInitial : store.read? sizeLocation = some (.word sizeValue))
    (exitOffset : exitLocation ≠ offsetLocation) (exitSize : exitLocation ≠ sizeLocation)
    (sizeOffset : sizeLocation ≠ offsetLocation) :
    Evaluates environment store (stop.rename mapping) (.inLeft .unit (.word Word.maximum))
      (haltCells exitLocation offsetLocation sizeLocation store) := by
  let locations : Locations := ⟨0, 0, 0, 0, exitLocation, offsetLocation, sizeLocation, memorySizeLocation⟩
  change Evaluates environment store (stop.rename mapping) (.inLeft .unit (.word Word.maximum)) (haltStore locations store)
  obtain ⟨memorySize, exit, offset, size, memoryCompiled, exitCompiled, offsetCompiled, sizeCompiled, rfl⟩ := stop_components compiled
  obtain ⟨memoryIndex, rfl, memoryFound⟩ := reference_position runtime memorySizeMember memoryCompiled
  obtain ⟨exitIndex, rfl, exitFound⟩ := reference_position runtime exitMember exitCompiled
  obtain ⟨offsetIndex, rfl, offsetFound⟩ := reference_position runtime offsetMember offsetCompiled
  obtain ⟨sizeIndex, rfl, sizeFound⟩ := reference_position runtime sizeMember sizeCompiled
  have offsetWritten : store.write? locations.returnOffset (.word Word.zero) =
      some (offsetStore locations store) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp offsetRead).1, rfl⟩
  have sizeRead : (offsetStore locations store).read? locations.returnSize = some (.word sizeValue) := by
    rw [Store.write?_preserves_other offsetWritten sizeOffset]
    exact sizeInitial
  have sizeWritten : (offsetStore locations store).write? locations.returnSize (.word Word.zero) =
      some (sizeStore locations store) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeRead).1, rfl⟩
  have exitRead : (sizeStore locations store).read? locations.exit =
      some (.word exitValue) := by
    rw [Store.write?_preserves_other sizeWritten exitSize, Store.write?_preserves_other offsetWritten exitOffset]
    exact exitInitial
  have exitWritten : (sizeStore locations store).write?
      locations.exit (.word (Word.ofNatModulo 3)) = some (haltStore locations store) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp exitRead).1, rfl⟩
  simp [LocalSequence.discard, LanguageResult.bind, List.foldr_cons, List.foldr_nil,
    Core.Expr.weakenAt, Core.Expr.rename, Renaming.lift, LanguageResult.failure, Nat.add_assoc]
  apply Evaluates.caseRight
  · unfold Memory.touch
    simp only [Core.Expr.rename]
    apply Evaluates.letE (.pair (.var memoryFound) (.pair .word .word))
    exact .ifTrue (.binary (.second (.second (.var rfl))) .word rfl) (.inRight .unit)
  · apply Evaluates.letE (bodyStore := store.set locations.returnOffset (.word Word.zero))
    · exact .storeCell (.var (by simpa [Renaming.lift] using offsetFound)) offsetRead .word offsetWritten
    · apply Evaluates.letE (bodyStore := (offsetStore locations store).set locations.returnSize (.word Word.zero))
      · exact .storeCell (.var (by simpa [Renaming.lift, Nat.add_assoc] using sizeFound)) sizeRead .word sizeWritten
      · apply Evaluates.letE (bodyStore := haltStore locations store)
        · exact .storeCell (.var (by simpa [Renaming.lift, Nat.add_assoc] using exitFound)) exitRead .word exitWritten
        · exact .inLeft .word


theorem stop_evaluates {scope : Scope} {stop : Core.Expr}
    (compiled : Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StateRel locations state store) :
    Evaluates environment store (stop.rename mapping) (.inLeft .unit (.word Word.maximum)) (haltStore locations store) := by
  have distinct := stateRelated.distinct
  simp [Locations.all] at distinct
  exact stop_evaluates_cells compiled runtime memorySizeMember exitMember offsetMember sizeMember
    stateRelated.exit stateRelated.returnOffset stateRelated.returnSize
    (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all)


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
    (stateRelated : StateRel locations state store)
    (key value : Word)
    (keyEvaluated : Evaluates environment store (keyExpr.rename mapping) (.word key) store)
    (valueEvaluated : Evaluates environment store (valueExpr.rename mapping) (.word value) store) :
    ∃ target final,
      ResultRel lowered.type (StorageSemantics.store state key value transient).1 target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧
      StateRel locations (StorageSemantics.store state key value transient).2 final ∧ Frame locations store final := by
  obtain ⟨static, stop, world, address, complete, staticCompiled, stopCompiled, worldCompiled,
    addressCompiled, completeCompiled, rfl⟩ := store_components transient compiled
  have staticRead := stateRelated.isStatic
  cases permitted : state.isStatic
  · rw [permitted] at staticRead
    obtain ⟨final, evaluated, worldRelated, frame⟩ := StorageCorrespondence.writeStorage_preserves state.address state.complete key value transient
      (.pair (reference_evaluates runtime worldMember worldCompiled store)
        (.pair (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
          (.pair (.loadCell (reference_evaluates runtime completeMember completeCompiled store) stateRelated.complete)
            (.pair keyEvaluated valueEvaluated)))) stateRelated.world
    refine ⟨_, final, store_result state key value transient permitted, ?_, ?_, Frame.of_storage frame⟩
    · apply Evaluates.ifFalse (.loadCell (reference_evaluates runtime staticMember staticCompiled store) staticRead)
      rw [writeStorage_rename]
      exact evaluated
    · rw [store_state state key value transient permitted]
      exact stateRelated.withWorld worldRelated frame
  · rw [permitted] at staticRead
    refine ⟨.inLeft .unit (.word Word.maximum), haltStore locations store, ?_, ?_, ?_, haltStore_frame _ _⟩
    · simpa only [StorageSemantics.store, permitted, ↓reduceIte] using (ResultRel.language (type := .unit) Word.maximum)
    · apply Evaluates.ifTrue (.loadCell (reference_evaluates runtime staticMember staticCompiled store) staticRead)
      exact stop_evaluates stopCompiled runtime memorySizeMember exitMember offsetMember sizeMember stateRelated
    · simpa only [StorageSemantics.store, permitted, ↓reduceIte] using stateRelated.halt

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
    (stateRelated : StateRel locations state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store)
    (sourceType : Ty) :
    ∃ result finalState target finalStore,
      StorageSemantics.builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      StateRel locations finalState finalStore ∧ Frame locations store finalStore := by
  have supported : Effects.supports operation.name = true := by
    cases operation with | load transient | store transient => cases transient <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  cases operation with
  | load transient =>
      obtain ⟨keyExpr, key, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨target, final, resultRelated, evaluated, finalRelated, frame⟩ := load_preserves transient rawCompiled
        (runtime.temporary .word (.word key)) worldMember addressMember completeMember stateRelated key (.var rfl)
      cases typed
      cases loweredEqual
      refine ⟨(StorageSemantics.load state key transient).1, (StorageSemantics.load state key transient).2,
        target, final, ?_, resultRelated, ?_, finalRelated, frame⟩
      · cases transient <;> rfl
      · exact LanguageResult.bind_success _ packed evaluated
  | store transient =>
      obtain ⟨keyExpr, valueExpr, key, value, rfl, rfl, rfl⟩ := two_words related words arity
      obtain ⟨target, final, resultRelated, evaluated, finalRelated, frame⟩ := store_preserves transient rawCompiled
        (runtime.temporary (.product .word .word) (.pair (.word key) (.word value)))
        worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
        stateRelated key value (.first (.var rfl)) (.second (.var rfl))
      cases typed
      cases loweredEqual
      refine ⟨(StorageSemantics.store state key value transient).1, (StorageSemantics.store state key value transient).2,
        target, final, ?_, resultRelated, ?_, finalRelated, frame⟩
      · cases transient <;> rfl
      · exact LanguageResult.bind_success _ packed evaluated

end Solcore.Frontend.RustHull.StorageBuiltinCorrespondence
