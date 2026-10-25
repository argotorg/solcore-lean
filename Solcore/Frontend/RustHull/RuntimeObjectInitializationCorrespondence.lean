import Solcore.Frontend.RustHull.RuntimeCompletionCorrespondence
import Solcore.Frontend.RustHull.RuntimeClosureCorrespondence
import Solcore.Frontend.RustHull.RuntimeMemoryInitializationCorrespondence

/-! The actual object wrapper captures its frame closures, installs callback
closures in fresh cells, and enters the same frame initializer as execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

/-- A structural property of emitted callback syntax. -/
def LambdaCode (code : Code) : Prop :=
  ∀ depth, ∃ parameter result body, code depth = Core.Expr.lambda parameter result body

theorem LambdaCode.evaluates {code : Code} (lambda : LambdaCode code)
    (depth : Nat) (environment : Core.Environment) (store : Core.Store) :
    ∃ value, Core.Evaluates environment store (code depth) value store := by
  obtain ⟨parameter, result, body, same⟩ := lambda depth
  exact ⟨.closure parameter result body environment, same ▸ Core.Evaluates.lambda⟩

theorem objectHandlers_lambdas (slots : List (String × Core.Ty)) (count : Nat)
    (images : List (Nat × List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator : Code) :
    LambdaCode (AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).1 ∧
    LambdaCode (AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).2 := by
  constructor <;> intro depth <;> exact ⟨_, _, _, rfl⟩

/-- Both callback cells are allocated and populated by their actual emitted
operations. All prior cells and all lexical values remain available to the
continuation. -/
theorem allocateCallbacks_initializes {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} {handlers : Code → Code → Code × Code}
    (closures : ∀ dispatcher creator, LambdaCode (handlers dispatcher creator).1 ∧ LambdaCode (handlers dispatcher creator).2) :
    ∃ dispatcher creator extra allocated,
      extra.length = 4 ∧ StoreRetains initial allocated ∧
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length) ∧
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)) ∧
      (∃ value, allocated.read? (initial.length + 1) = some value) ∧
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
  obtain ⟨dispatchClosure, dispatchEvaluated⟩ := ((closures dispatcher creator).1).evaluates
    (depth + 2) (creatorValue :: dispatcherValue :: environment) allocated
  let stored : Core.Store := allocated.set initial.length (.inRight .unit dispatchClosure)
  have dispatchFound : allocated.read? initial.length = some (.inLeft AccountRuntime.dispatchCallbackType .unit) := by
    simp [allocated, Core.Store.read?]
  have dispatchWritten : allocated.write? initial.length (.inRight .unit dispatchClosure) = some stored :=
    Core.Store.write?_eq_some_iff.mpr ⟨by simp [allocated], rfl⟩
  obtain ⟨createClosure, createEvaluated⟩ := ((closures dispatcher creator).2).evaluates
    (depth + 3) (.unit :: creatorValue :: dispatcherValue :: environment) stored
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
    creatorRelated.prepend [Core.Value.unit, .unit], ⟨_, Core.Store.write?_reads_written createWritten⟩, ?_⟩
  intro continuation result final completed
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

theorem allocateCallbacks_evaluates {depth : Nat} {environment : Core.Environment}
    {initial final : Core.Store} {result : Core.Value}
    {handlers : Code → Code → Code × Code} {continuation : Code → Code → Code}
    (closures : ∀ dispatcher creator, LambdaCode (handlers dispatcher creator).1 ∧ LambdaCode (handlers dispatcher creator).2)
    (continued : ∀ dispatcher creator extra allocated,
      extra.length = 4 → StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)) →
      (∃ value, allocated.read? (initial.length + 1) = some value) →
      Core.Evaluates (extra ++ environment) allocated
        (continuation dispatcher creator (depth + extra.length)) result final) :
    Core.Evaluates environment initial (AccountRuntime.allocateCallbacks handlers continuation depth) result final := by
  obtain ⟨dispatcher, creator, extra, allocated, length, retained, dispatcherValue, creatorValue, creatorFound, evaluated⟩ :=
    allocateCallbacks_initializes (depth := depth) (environment := environment) (initial := initial) closures
  exact evaluated continuation result final
    (continued dispatcher creator extra allocated length retained dispatcherValue creatorValue creatorFound)

inductive CapturedClosures (environment : Core.Environment) : List Core.Expr → List Core.Value → Prop where
  | nil : CapturedClosures environment [] []
  | cons {expression expressions value values} (head : CapturedClosure expression environment value)
      (tail : CapturedClosures environment expressions values) :
      CapturedClosures environment (expression :: expressions) (value :: values)

theorem CapturedClosures.evaluates {environment : Core.Environment} {expressions : List Core.Expr}
    {values : List Core.Value} (related : CapturedClosures environment expressions values) (store : Core.Store) :
    Core.Evaluates environment store (bundle expressions) (bundleValues values) store := by
  induction related with
  | nil => exact .unit
  | cons head tail ih =>
      cases tail with
      | nil => exact head.evaluates store
      | cons next rest => exact .pair (head.evaluates store) ih

theorem compileFrame_captures {program : Program} {code : CodeBlock}
    {slots : List (String × Core.Ty)} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code slots fuel = .ok compiled)
    (environment : Core.Environment) : ∃ value, CapturedClosure compiled environment value := by
  obtain ⟨_, _, _, _, _, rfl⟩ := compileFrame_components accepted
  exact ⟨_, .lambda _ _ _ _⟩

theorem InitializedCells.retained {cells : List InitializedCell} {initial final : Core.Store}
    (initialized : InitializedCells cells initial) (retained : StoreRetains initial final) :
    InitializedCells cells final := by
  intro cell member
  have found := initialized cell member
  rw [retained.read cell.location (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- Frame closures, shared state and callback cells are created by the actual
object wrapper. The remaining continuation is precisely its top-level frame. -/
theorem objectRuntime_evaluates {depth : Nat} {environment : Core.Environment}
    {initial final : Core.Store} {result : Core.Value}
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
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final) :
    Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  unfold AccountRuntime.objectRuntime CodeBuilder.bind
  apply Core.Evaluates.letE bundleEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, description, sharedEvaluated⟩ :=
    allocateSharedSlots_initializes sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member)
  apply sharedEvaluated
  apply allocateCallbacks_evaluates
    (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  intro dispatcher creator callbackExtra allocated _ callbacksRetained dispatcherRelated creatorRelated creatorRead
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  have completed := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) creatorRead
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

theorem objectRuntime_evaluates_some {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} {result : Core.Value}
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
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      ∃ final, Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, description, sharedEvaluated⟩ :=
    allocateSharedSlots_initializes sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member)
  obtain ⟨dispatcher, creator, callbackExtra, allocated, _, callbacksRetained, dispatcherRelated, creatorRelated, creatorRead, callbacksEvaluated⟩ :=
    allocateCallbacks_initializes (depth := depth + 1 + sharedExtra.length)
      (environment := sharedExtra ++ bundleValues functionsValue :: environment) (initial := initial ++ suffix)
      (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  obtain ⟨final, completed⟩ := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) creatorRead
  refine ⟨final, Core.Evaluates.letE bundleEvaluated ?_⟩
  apply sharedEvaluated
  apply callbacksEvaluated
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

theorem objectRuntime_evaluates_result {depth : Nat} {environment : Core.Environment}
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
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
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
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, description, sharedEvaluated⟩ :=
    allocateSharedSlots_initializes sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member)
  obtain ⟨dispatcher, creator, callbackExtra, allocated, _, callbacksRetained, dispatcherRelated, creatorRelated, creatorRead, callbacksEvaluated⟩ :=
    allocateCallbacks_initializes (depth := depth + 1 + sharedExtra.length)
      (environment := sharedExtra ++ bundleValues functionsValue :: environment) (initial := initial ++ suffix)
      (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
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
    initializedFinal descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) creatorRead
  refine ⟨result, final, Core.Evaluates.letE bundleEvaluated ?_, observed⟩
  apply sharedEvaluated
  apply callbacksEvaluated
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

end Solcore.Frontend.RustHull.Correspondence
