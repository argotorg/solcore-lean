import Solcore.Frontend.RustHull.AccountRuntime
import Solcore.Frontend.RustHull.RuntimeCodeCorrespondence
import Solcore.Frontend.RustHull.MemoryCorrespondence
import Solcore.Frontend.RustHull.EffectEnvironmentCorrespondence

/-! The actual runtime allocation builders establish the initial cell values
and reference arguments used by compiled Hull frames. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

structure InitializedCell where
  name : String
  type : Core.Ty
  location : Nat
  value : Core.Value

def InitializedCell.reference (cell : InitializedCell) : Core.Value :=
  .cellRef cell.type cell.location

def InitializedCells (cells : List InitializedCell) (store : Core.Store) : Prop :=
  ∀ cell ∈ cells, store.read? cell.location = some cell.value

structure RuntimeReferences (depth : Nat) (environment : Core.Environment)
    (references : AccountRuntime.References) (cells : List InitializedCell) : Prop where
  names : references.map Prod.fst = cells.map InitializedCell.name
  values : CodeValues depth environment (references.map Prod.snd) (cells.map InitializedCell.reference)

theorem RuntimeReferences.prepend {depth : Nat} {environment : Core.Environment}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells) (extra : Core.Environment) :
    RuntimeReferences (depth + extra.length) (extra ++ environment) references cells :=
  ⟨related.names, related.values.prepend extra⟩

theorem InitializedCells.appendStore {cells : List InitializedCell} {store : Core.Store}
    (initialized : InitializedCells cells store) (suffix : Core.Store) :
    InitializedCells cells (store ++ suffix) := by
  intro cell member
  have found := initialized cell member
  have bound : cell.location < store.length := List.getElem?_eq_some_iff.mp found |>.1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using found

theorem InitializedCells.cons {cells : List InitializedCell} {store : Core.Store}
    (initialized : InitializedCells cells store) (name : String) (type : Core.Ty) (value : Core.Value) :
    InitializedCells (⟨name, type, store.length, value⟩ :: cells) (store ++ [value]) := by
  intro cell member
  cases member with
  | head => simp [Core.Store.read?]
  | tail _ member => exact initialized.appendStore [value] cell member

theorem sharedInitializers_values {depth : Nat} {environment : Core.Environment}
    {context : Code} {values ambient : List Core.Value} {world complete balances : Core.Value}
    (related : CodeValue depth environment context (bundleValues values))
    (length : values.length = 12) (ambientLength : ambient.length = Ambient.slots.length)
    (worldFound : values[7]? = some world) (completeFound : values[9]? = some complete)
    (balancesFound : values[6]? = some balances) (ambientFound : values[10]? = some (bundleValues ambient)) :
    CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2))
      ([world, complete, Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0), balances] ++ ambient) := by
  have ambientRelated : CodeValue depth environment (part 10 12 context) (bundleValues ambient) := by
    simpa only [length] using related.part ambientFound
  have ambientCodes : CodeValues depth environment
      (Ambient.slots.zipIdx.map (fun entry => part entry.2 Ambient.slots.length (part 10 12 context))) ambient := by
    apply CodeValues.of_getElem? (by simpa only [List.length_map, List.length_zipIdx] using ambientLength.symm)
    intro index code value codeFound valueFound
    simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Nat.zero_add] at codeFound
    obtain ⟨slot, _, same⟩ := Option.map_eq_some_iff.mp codeFound
    subst code
    simpa only [ambientLength, Function.comp_apply] using ambientRelated.part valueFound
  have heads : CodeValues depth environment
      [part 7 12 context, part 9 12 context, empty, number 0, part 6 12 context]
      [world, complete, Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0), balances] :=
    .cons (by simpa only [length] using related.part worldFound)
      (.cons (by simpa only [length] using related.part completeFound)
        (.cons (CodeValue.empty depth environment)
          (.cons (CodeValue.number 0 depth environment)
            (.cons (by simpa only [length] using related.part balancesFound) .nil))))
  simpa only [AccountRuntime.sharedInitializers, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def] using heads.append ambientCodes

/-- Every emitted shared allocation is executed before its continuation. The
returned references and stored values include the real allocated locations. -/
theorem allocateSharedSlots_initializes
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {initializers : List (String × Core.Ty × Code)} {initialValues : List Core.Value}
    (inputs : CodeValues depth environment (initializers.map (·.2.2)) initialValues)
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells)
    (initialized : InitializedCells cells store) :
    ∃ extra suffix finalReferences finalCells,
      RuntimeReferences (depth + extra.length) (extra ++ environment) finalReferences finalCells ∧
      InitializedCells finalCells (store ++ suffix) ∧
      finalCells.map (fun cell => (cell.name, cell.type, cell.value)) =
        ((initializers.zip initialValues).map (fun (entry, value) => (entry.1, entry.2.1, value))).reverse ++
          cells.map (fun cell => (cell.name, cell.type, cell.value)) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation finalReferences (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateSharedSlots continuation initializers references depth) result finalStore := by
  induction initializers generalizing depth environment store initialValues references cells with
  | nil =>
      cases inputs
      refine ⟨[], [], references, cells, ?_, ?_, rfl, ?_⟩
      · simpa using related
      · simpa using initialized
      · intro continuation result finalStore evaluated
        simpa [AccountRuntime.allocateSharedSlots] using evaluated
  | cons entry rest ih =>
      rcases entry with ⟨name, type, code⟩
      cases inputs with
      | @cons _ value _ values head tail =>
          let reference : Core.Value := .cellRef type store.length
          let bound : Code := fun here => .var (here - depth - 1)
          let cell : InitializedCell := ⟨name, type, store.length, value⟩
          have earlier := related.prepend [reference]
          have nextRelated : RuntimeReferences (depth + 1) (reference :: environment)
              ((name, bound) :: references) (cell :: cells) := by
            refine ⟨congrArg (name :: ·) related.names, .cons ?_ ?_⟩
            · exact CodeValue.bound depth environment reference
            · simpa using earlier.values
          obtain ⟨extra, suffix, finalReferences, finalCells, finalRelated, finalInitialized, description, evaluated⟩ :=
            ih (by simpa using tail.prepend [reference]) nextRelated (initialized.cons name type value)
          refine ⟨extra ++ [reference], [value] ++ suffix, finalReferences, finalCells, ?_, ?_, ?_, ?_⟩
          · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using finalRelated
          · simpa only [List.append_assoc] using finalInitialized
          · simpa only [List.zip_cons_cons, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append, cell] using description
          · intro continuation result finalStore completed
            apply Core.Evaluates.letE (.newCell (head.evaluates store))
            apply evaluated continuation result finalStore
            simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

def FrameInitializersReady (depth : Nat) (environment : Core.Environment)
    (frame dispatcher gas code codeSize codeKnown : Code) : Prop :=
  ∀ extra name store, ∃ value, Core.Evaluates (extra ++ environment) store
    (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown (depth + extra.length)) value store

theorem frameInitializers_ready {depth : Nat} {environment : Core.Environment}
    {frame dispatcher gas code codeSize codeKnown : Code} {values : List Core.Value}
    {gasValue codeValue sizeValue knownValue : Core.Value}
    (frameRelated : CodeValue depth environment frame (bundleValues values))
    (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersReady depth environment frame dispatcher gas code codeSize codeKnown := by
  intro extra name store
  have projected : ∀ index, index < 8 → ∃ value, Core.Evaluates (extra ++ environment) store
      (part index 8 frame (depth + extra.length)) value store := by
    intro index bound
    have existsValue := List.getElem?_eq_getElem (l := values) (i := index) (by omega)
    refine ⟨values[index], ?_⟩
    simpa only [length, part] using projectArgument_evaluates (frameRelated extra store) existsValue
  unfold AccountRuntime.frameInitial
  split <;> first
    | exact ⟨_, .construct .unit⟩
    | exact ⟨_, .word⟩
    | exact ⟨_, .inRight .lambda⟩
    | exact ⟨_, gasRelated extra store⟩
    | exact ⟨_, codeRelated extra store⟩
    | exact ⟨_, sizeRelated extra store⟩
    | exact ⟨_, knownRelated extra store⟩
    | exact projected 0 (by decide)
    | exact projected 1 (by decide)
    | exact projected 2 (by decide)
    | exact projected 3 (by decide)
    | exact projected 4 (by decide)
    | exact projected 6 (by decide)
    | exact projected 7 (by decide)

theorem FrameInitializersReady.prepend {depth : Nat} {environment : Core.Environment}
    {frame dispatcher gas code codeSize codeKnown : Code}
    (ready : FrameInitializersReady depth environment frame dispatcher gas code codeSize codeKnown)
    (earlier : Core.Environment) :
    FrameInitializersReady (depth + earlier.length) (earlier ++ environment) frame dispatcher gas code codeSize codeKnown := by
  intro extra name store
  simpa only [List.append_assoc, List.length_append, Nat.add_assoc, Nat.add_comm earlier.length extra.length]
    using ready (extra ++ earlier) name store

def RuntimeCellReady (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (name : String) (type : Core.Ty) (code : Code) : Prop :=
  ∃ cell : InitializedCell, cell.name = name ∧ cell.type = type ∧
    CodeValue depth environment code cell.reference ∧ store.read? cell.location = some cell.value

theorem RuntimeCellReady.extend {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {name : String} {type : Core.Ty} {code : Code}
    (ready : RuntimeCellReady depth environment store name type code)
    (earlier : Core.Environment) (suffix : Core.Store) :
    RuntimeCellReady (depth + earlier.length) (earlier ++ environment) (store ++ suffix) name type code := by
  obtain ⟨cell, named, typed, related, stored⟩ := ready
  refine ⟨cell, named, typed, related.prepend earlier, ?_⟩
  have bound := (List.getElem?_eq_some_iff.mp stored).1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using stored

def FrameSharedReady (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (slots : List (String × Core.Ty)) (shared : AccountRuntime.References) : Prop :=
  ∀ slot ∈ slots, ∀ name code, shared.find? (·.1 == slot.1) = some (name, code) →
    RuntimeCellReady depth environment store slot.1 slot.2 code

def FrameCreatorReady (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (slots : List (String × Core.Ty)) (creator : Code) : Prop :=
  ∀ type, ("createHandler", type) ∈ slots → RuntimeCellReady depth environment store "createHandler" type creator

/-- The full frame allocator retains shared locations, reuses the creator cell,
and allocates every other slot before passing the actual reference list on. -/
theorem allocateFrameSlots_initializes
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    (initializers : FrameInitializersReady depth environment frame dispatcher gas code codeSize codeKnown)
    (sharedReady : FrameSharedReady depth environment store slots shared)
    (creatorReady : FrameCreatorReady depth environment store slots creator)
    {previous : List Code} {previousCells : List InitializedCell}
    (previousRelated : CodeValues depth environment previous (previousCells.map InitializedCell.reference))
    (previousStored : InitializedCells previousCells store) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((previousCells.reverse ++ cells).map InitializedCell.reference) ∧
      InitializedCells (previousCells.reverse ++ cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrameSlots shared frame dispatcher creator gas code codeSize codeKnown
            continuation slots previous depth) result finalStore := by
  induction slots generalizing depth environment store previous previousCells with
  | nil =>
      refine ⟨[], [], previous.reverse, [], ?_, ?_, rfl, ?_⟩
      · simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil, List.map_reverse]
          using previousRelated.reverse
      · intro cell member
        simpa only [List.append_nil] using previousStored cell (by simpa using member)
      · intro continuation result finalStore evaluated
        simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil,
          AccountRuntime.allocateFrameSlots] using evaluated
  | cons slot rest ih =>
      rcases slot with ⟨name, type⟩
      have sharedTail : FrameSharedReady depth environment store rest shared := by
        intro slot member
        exact sharedReady slot (.tail _ member)
      have creatorTail : FrameCreatorReady depth environment store rest creator := by
        intro type member
        exact creatorReady type (.tail _ member)
      cases found : shared.find? (·.1 == name) with
      | some entry =>
          rcases entry with ⟨foundName, reference⟩
          obtain ⟨cell, named, typed, related, stored⟩ := sharedReady (name, type) (.head _) foundName reference found
          have storedCons : InitializedCells (cell :: previousCells) store := by
            intro selected member
            cases member with
            | head => exact stored
            | tail _ member => exact previousStored selected member
          obtain ⟨extra, suffix, references, cells, related', stored', signature, evaluated⟩ :=
            ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
          refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_⟩
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
          · simp only [List.map_cons, named, typed, signature]
          · intro continuation result finalStore completed
            simpa only [AccountRuntime.allocateFrameSlots, found] using evaluated continuation result finalStore completed
      | none =>
          by_cases isCreator : name == "createHandler"
          · have named : name = "createHandler" := by simpa only [beq_iff_eq] using isCreator
            subst name
            obtain ⟨cell, named, typed, related, stored⟩ := creatorReady type (.head _)
            have storedCons : InitializedCells (cell :: previousCells) store := by
              intro selected member
              cases member with
              | head => exact stored
              | tail _ member => exact previousStored selected member
            obtain ⟨extra, suffix, references, cells, related', stored', signature, evaluated⟩ :=
              ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
            refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_⟩
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
            · simp only [List.map_cons, named, typed, signature]
            · intro continuation result finalStore completed
              simpa only [AccountRuntime.allocateFrameSlots, found, beq_self_eq_true, ↓reduceIte]
                using evaluated continuation result finalStore completed
          · obtain ⟨value, initialized⟩ := initializers [] name store
            have initialized' : Core.Evaluates environment store
                (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown depth) value store := by
              simpa using initialized
            let reference : Core.Value := .cellRef type store.length
            let cell : InitializedCell := ⟨name, type, store.length, value⟩
            have sharedTail' : FrameSharedReady (depth + 1) (reference :: environment) (store ++ [value]) rest shared := by
              intro slot member foundName foundCode found'
              simpa using (sharedTail slot member foundName foundCode found').extend [reference] [value]
            have creatorTail' : FrameCreatorReady (depth + 1) (reference :: environment) (store ++ [value]) rest creator := by
              intro type member
              simpa using (creatorTail type member).extend [reference] [value]
            have relatedCons : CodeValues (depth + 1) (reference :: environment)
                ((fun here => .var (here - depth - 1)) :: previous) ((cell :: previousCells).map InitializedCell.reference) :=
              .cons (CodeValue.bound depth environment reference) (by simpa using previousRelated.prepend [reference])
            obtain ⟨extra, suffix, references, cells, related', stored', signature, evaluated⟩ :=
              ih (by simpa using initializers.prepend [reference]) sharedTail' creatorTail'
                relatedCons (previousStored.cons name type value)
            refine ⟨extra ++ [reference], [value] ++ suffix, references, cell :: cells, ?_, ?_, ?_, ?_⟩
            · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1, List.reverse_cons] using related'
            · simpa [List.append_assoc, List.reverse_cons] using stored'
            · exact congrArg ((name, type) :: ·) signature
            · intro continuation result finalStore completed
              simp only [AccountRuntime.allocateFrameSlots, found, isCreator]
              apply Core.Evaluates.letE (.newCell initialized')
              apply evaluated continuation result finalStore
              simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

def initialMemoryCell (store : Core.Store) : InitializedCell :=
  ⟨"memory", Core.WordMapping.type, store.length, Core.WordMapping.encode []⟩

def initialSizeCell (store : Core.Store) : InitializedCell :=
  ⟨"memorySize", .word, store.length + 1, .word (Core.Word.ofNatModulo 0)⟩

/-- The runtime's first two frame cells establish empty memory and size zero.
The remaining real allocations preserve those cells and supply every actual
frame argument to the continuation. -/
theorem allocateFrame_memory_initializes
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    (initializers : FrameInitializersReady depth environment frame dispatcher gas code codeSize codeKnown)
    (sharedReady : FrameSharedReady depth environment store slots shared)
    (creatorReady : FrameCreatorReady depth environment store slots creator)
    (memoryAbsent : shared.find? (·.1 == "memory") = none)
    (sizeAbsent : shared.find? (·.1 == "memorySize") = none) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((initialMemoryCell store :: initialSizeCell store :: cells).map InitializedCell.reference) ∧
      InitializedCells (initialMemoryCell store :: initialSizeCell store :: cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      MemoryCorrespondence.StateRel store.length (store.length + 1) ⟨[], Core.Word.ofNatModulo 0⟩ (store ++ suffix) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrame (("memory", Core.WordMapping.type) :: ("memorySize", .word) :: slots)
            shared frame dispatcher creator gas code codeSize codeKnown continuation depth) result finalStore := by
  let memoryValue := Core.WordMapping.encode []
  let sizeValue := Core.Value.word (Core.Word.ofNatModulo 0)
  let memoryReference := (initialMemoryCell store).reference
  let sizeReference := (initialSizeCell store).reference
  let previous : List Code :=
    [fun here => .var (here - (depth + 1) - 1), fun here => .var (here - depth - 1)]
  have sharedReady' : FrameSharedReady (depth + 2) (sizeReference :: memoryReference :: environment)
      (store ++ [memoryValue, sizeValue]) slots shared := by
    intro slot member name code found
    simpa using (sharedReady slot member name code found).extend [sizeReference, memoryReference] [memoryValue, sizeValue]
  have creatorReady' : FrameCreatorReady (depth + 2) (sizeReference :: memoryReference :: environment)
      (store ++ [memoryValue, sizeValue]) slots creator := by
    intro type member
    simpa using (creatorReady type member).extend [sizeReference, memoryReference] [memoryValue, sizeValue]
  have previousRelated : CodeValues (depth + 2) (sizeReference :: memoryReference :: environment) previous
      ([initialSizeCell store, initialMemoryCell store].map InitializedCell.reference) := by
    refine .cons ?_ (.cons ?_ .nil)
    · simpa [Nat.add_assoc] using CodeValue.bound (depth + 1) (memoryReference :: environment) sizeReference
    · simpa [Nat.add_assoc] using (CodeValue.bound depth environment memoryReference).prepend [sizeReference]
  have previousStored : InitializedCells [initialSizeCell store, initialMemoryCell store]
      (store ++ [memoryValue, sizeValue]) := by
    intro cell member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [initialSizeCell, initialMemoryCell, Core.Store.read?,
      memoryValue, sizeValue]
  obtain ⟨extra, suffix, references, cells, related, stored, signature, evaluated⟩ :=
    allocateFrameSlots_initializes
      (by simpa using initializers.prepend [sizeReference, memoryReference]) sharedReady' creatorReady'
      previousRelated previousStored
  have initialized : InitializedCells (initialMemoryCell store :: initialSizeCell store :: cells)
      (store ++ ([memoryValue, sizeValue] ++ suffix)) := by
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.append_assoc, List.cons_append] using stored
  refine ⟨extra ++ [sizeReference, memoryReference], [memoryValue, sizeValue] ++ suffix, references, cells,
    ?_, initialized, signature, ?_, ?_⟩
  · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 2, List.reverse_cons] using related
  · exact ⟨by omega, initialized _ (.head _), initialized _ (.tail _ (.head _))⟩
  · intro continuation result finalStore completed
    simp only [AccountRuntime.allocateFrame, AccountRuntime.allocateFrameSlots, memoryAbsent, sizeAbsent]
    apply Core.Evaluates.letE (.newCell (.construct .unit))
    apply Core.Evaluates.letE (.newCell .word)
    have continued := evaluated continuation result finalStore
      (by simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 2] using completed)
    simpa [previous, memoryReference, sizeReference, initialMemoryCell, initialSizeCell,
      InitializedCell.reference, Core.Store.allocate, Nat.add_assoc, memoryValue, sizeValue, Core.WordMapping.encode] using continued

end Solcore.Frontend.RustHull.Correspondence
