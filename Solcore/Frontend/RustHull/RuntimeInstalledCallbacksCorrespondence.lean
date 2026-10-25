import Solcore.Frontend.RustHull.RuntimeObjectLocationsCorrespondence

/-! Actual callback installation exposes both captured closures and exact cell
contents for later calls through the public object runtime. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

theorem LambdaCode.captures {code : Code} (lambda : LambdaCode code)
    (depth : Nat) (environment : Core.Environment) :
    ∃ value, CapturedClosure (code depth) environment value := by
  obtain ⟨parameter, result, body, same⟩ := lambda depth
  exact ⟨.closure parameter result body environment, same ▸ CapturedClosure.lambda ..⟩

theorem allocateCallbacks_captures {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} {handlers : Code → Code → Code × Code}
    (closures : ∀ dispatcher creator, LambdaCode (handlers dispatcher creator).1 ∧ LambdaCode (handlers dispatcher creator).2) :
    ∃ dispatcher creator extra allocated,
      extra.length = 4 ∧ StoreRetains initial allocated ∧
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length) ∧
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)) ∧
      CodeValue (depth + 2)
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1) ::
          .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length :: environment)
        dispatcher (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length) ∧
      CodeValue (depth + 2)
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1) ::
          .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length :: environment)
        creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)) ∧
      (∃ dispatchClosure createClosure,
        CapturedClosure ((handlers dispatcher creator).1 (depth + 2))
          (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1) ::
            .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length :: environment) dispatchClosure ∧
        CapturedClosure ((handlers dispatcher creator).2 (depth + 3))
          (.unit :: .cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1) ::
            .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length :: environment) createClosure ∧
        allocated.read? initial.length = some (.inRight .unit dispatchClosure) ∧
        allocated.read? (initial.length + 1) = some (.inRight .unit createClosure)) ∧
      ∀ continuation result final,
        Core.Evaluates (extra ++ environment) allocated
          (continuation dispatcher creator (depth + extra.length)) result final →
        Core.Evaluates environment initial (AccountRuntime.allocateCallbacks handlers continuation depth) result final := by
  let dispatcher : Code := fun here => .var (here - depth - 1)
  let creator : Code := fun here => .var (here - (depth + 1) - 1)
  let dispatcherValue := Core.Value.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length
  let creatorValue := Core.Value.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)
  let allocated := initial ++ [Core.Value.inLeft AccountRuntime.dispatchCallbackType .unit,
    Core.Value.inLeft Creation.callbackType .unit]
  have dispatcherRelated := CodeValue.bound depth environment dispatcherValue
  have creatorRelated := CodeValue.bound (depth + 1) (dispatcherValue :: environment) creatorValue
  obtain ⟨dispatchClosure, dispatchCaptured⟩ := ((closures dispatcher creator).1).captures
    (depth + 2) (creatorValue :: dispatcherValue :: environment)
  have dispatchEvaluated := dispatchCaptured.evaluates allocated
  let stored : Core.Store := allocated.set initial.length (.inRight .unit dispatchClosure)
  have dispatchFound : allocated.read? initial.length = some (.inLeft AccountRuntime.dispatchCallbackType .unit) := by
    simp [allocated, Core.Store.read?]
  have dispatchWritten : allocated.write? initial.length (.inRight .unit dispatchClosure) = some stored :=
    Core.Store.write?_eq_some_iff.mpr ⟨by simp [allocated], rfl⟩
  obtain ⟨createClosure, createCaptured⟩ := ((closures dispatcher creator).2).captures
    (depth + 3) (.unit :: creatorValue :: dispatcherValue :: environment)
  have createEvaluated := createCaptured.evaluates stored
  let initialized : Core.Store := stored.set (initial.length + 1) (.inRight .unit createClosure)
  have createFound : stored.read? (initial.length + 1) = some (.inLeft Creation.callbackType .unit) := by
    rw [Core.Store.write?_preserves_other (location := initial.length) (otherLocation := initial.length + 1) dispatchWritten (Nat.succ_ne_self _)]
    simp [allocated, Core.Store.read?]
  have createWritten : stored.write? (initial.length + 1) (.inRight .unit createClosure) = some initialized :=
    Core.Store.write?_eq_some_iff.mpr ⟨by simp [stored, allocated], rfl⟩
  have retained : StoreRetains initial initialized := by
    constructor
    · simp [initialized, stored, allocated]
    · intro location bounded
      rw [Core.Store.write?_preserves_other (location := initial.length + 1) (otherLocation := location) createWritten (Nat.ne_of_lt (Nat.lt_trans bounded (Nat.lt_succ_self _))),
        Core.Store.write?_preserves_other (location := initial.length) (otherLocation := location) dispatchWritten (Nat.ne_of_lt bounded)]
      exact List.getElem?_append_left bounded
  refine ⟨dispatcher, creator, [Core.Value.unit, .unit, creatorValue, dispatcherValue], initialized,
    rfl, retained, dispatcherRelated.prepend [Core.Value.unit, .unit, creatorValue],
    creatorRelated.prepend [Core.Value.unit, .unit], dispatcherRelated.prepend [creatorValue], creatorRelated,
    ⟨dispatchClosure, createClosure, dispatchCaptured, createCaptured, ?_, Core.Store.write?_reads_written createWritten⟩, ?_⟩
  · rw [Core.Store.write?_preserves_other createWritten (Nat.ne_of_lt (Nat.lt_succ_self _))]
    exact Core.Store.write?_reads_written dispatchWritten
  · intro continuation result final completed
    unfold AccountRuntime.allocateCallbacks CodeBuilder.bind
    apply Core.Evaluates.letE (Core.OptionalCell.allocate_evaluates ..)
    have second := Core.OptionalCell.allocate_evaluates Creation.callbackType
      (dispatcherValue :: environment) (initial ++ [.inLeft AccountRuntime.dispatchCallbackType .unit])
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc] at second
    apply Core.Evaluates.letE second
    apply Core.Evaluates.letE
      (Core.Evaluates.storeCell (dispatcherRelated [creatorValue] allocated) dispatchFound
        (.inRight dispatchEvaluated) dispatchWritten)
    apply Core.Evaluates.letE
      (Core.Evaluates.storeCell (creatorRelated [Core.Value.unit] stored) createFound
        (.inRight createEvaluated) createWritten)
    exact completed

theorem shared_description_names {context : Code} {cells : List InitializedCell} {values : List Core.Value}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip values).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    (length : (AccountRuntime.sharedInitializers context).length ≤ values.length) :
    cells.map InitializedCell.name = (sharedSlotTypes.map Prod.fst).reverse := by
  have names := congrArg (List.map Prod.fst) description
  simp only [List.map_reverse, List.map_map, Function.comp_def] at names
  rw [names]
  have firsts := List.map_fst_zip length
  have mapped := congrArg (List.map Prod.fst) firsts
  simp only [List.map_map, Function.comp_def, sharedInitializers_names] at mapped
  exact congrArg List.reverse mapped

/-- Concrete code references and the actual shared cells at callback capture. -/
structure ObjectCallbackCapture (slots : List (String × Core.Ty)) (count : Nat)
    (images : List (Nat × List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (functionsValue : List Core.Value) (cells : List InitializedCell)
    (dispatcherLocation creatorLocation : Nat) (store : Core.Store) where
  depth : Nat
  environment : Core.Environment
  functions : Code
  shared : AccountRuntime.References
  dispatcher : Code
  creator : Code
  functionValues : CodeValue depth environment functions (bundleValues functionsValue)
  names : cells.map InitializedCell.name = (sharedSlotTypes.map Prod.fst).reverse
  references : RuntimeReferences depth environment shared cells
  dispatcherValue : CodeValue depth environment dispatcher
    (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation)
  creatorValue : CodeValue depth environment creator
    (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation)
  closure : Core.Value
  captured : CapturedClosure
    ((AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).1 depth)
    environment closure
  stored : store.read? dispatcherLocation = some (.inRight .unit closure)


theorem objectRuntime_evaluates_callbacks {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} (observes : Core.Value → Core.Store → Prop)
    {slots : List (String × Core.Ty)} {compiled : Core.Expr} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {context : Code}
    {functionsValue initialValues : List Core.Value}
    (captured : CapturedClosures environment (compiled :: others) functionsValue)
    (inputs : CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2)) initialValues)
    (continued : ∀ functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation,
      CodeValue (depth + extra.length) (extra ++ environment) functions (bundleValues functionsValue) →
      RuntimeReferences (depth + extra.length) (extra ++ environment) shared cells →
      InitializedCells cells allocated →
      CellLocations cells →
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      (∀ cell ∈ cells, cell.location < creatorLocation) →
      (∀ cell ∈ cells, cell.location < dispatcherLocation) →
      dispatcherLocation < creatorLocation →
      ObjectCallbackCapture slots (others.length + 1) images catalog functionsValue cells
        dispatcherLocation creatorLocation allocated →
      ∃ result final, Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final ∧ observes result final) :
    ∃ result final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final ∧ observes result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, separate, description, sharedEvaluated⟩ :=
    allocateSharedSlots_separates sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member) CellLocations.nil
  obtain ⟨dispatcher, creator, callbackExtra, allocated, _, callbacksRetained, dispatcherRelated, creatorRelated, dispatcherCaptured, creatorCaptured, capturedCallbacks, callbacksEvaluated⟩ :=
    allocateCallbacks_captures (depth := depth + 1 + sharedExtra.length)
      (environment := sharedExtra ++ bundleValues functionsValue :: environment) (initial := initial ++ suffix)
      (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  obtain ⟨dispatchClosure, createClosure, dispatchCapture, _, dispatchRead, creatorRead⟩ := capturedCallbacks
  let callbackCapture : ObjectCallbackCapture slots (others.length + 1) images catalog functionsValue cells
      (initial ++ suffix).length ((initial ++ suffix).length + 1) allocated := {
    depth := depth + 1 + sharedExtra.length + 2
    environment := .cellRef (Core.OptionalCell.cellType Creation.callbackType) ((initial ++ suffix).length + 1) ::
      .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) (initial ++ suffix).length ::
      sharedExtra ++ bundleValues functionsValue :: environment
    functions := functions
    shared := shared
    dispatcher := dispatcher
    creator := creator
    functionValues := (functionsRelated.prepend sharedExtra).prepend
      [.cellRef (Core.OptionalCell.cellType Creation.callbackType) ((initial ++ suffix).length + 1),
       .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) (initial ++ suffix).length]
    names := shared_description_names
      (by simpa only [List.map_nil, List.append_nil] using description)
      (by simpa only [List.length_map] using Nat.le_of_eq inputs.length)
    references := references.prepend
      [.cellRef (Core.OptionalCell.cellType Creation.callbackType) ((initial ++ suffix).length + 1),
       .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) (initial ++ suffix).length]
    dispatcherValue := dispatcherCaptured
    creatorValue := creatorCaptured
    closure := dispatchClosure
    captured := dispatchCapture
    stored := dispatchRead }
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  obtain ⟨result, final, completed, observed⟩ := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal separate descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) ⟨_, creatorRead⟩
    (fun cell member => Nat.lt_trans (initialized.location_bound member) (Nat.lt_succ_self _))
    (fun _ member => initialized.location_bound member) (Nat.lt_succ_self _) callbackCapture
  refine ⟨result, final, Core.Evaluates.letE bundleEvaluated ?_, observed⟩
  apply sharedEvaluated
  apply callbacksEvaluated
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

end Solcore.Frontend.RustHull.Correspondence
