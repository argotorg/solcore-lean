import Solcore.Frontend.RustHull.RuntimeMemoryInitializationCorrespondence

/-! Frame initialization records the values and disjoint locations needed by
public execution, as well as evaluating the actual allocation builders. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

def FrameInitializersValid (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (frame dispatcher gas code codeSize codeKnown : Code) (shared : AccountRuntime.References) (property : InitializedCell → Prop) : Prop :=
  ∀ extra suffix name type, shared.find? (·.1 == name) = none → ∃ value, Core.Evaluates (extra ++ environment) (store ++ suffix)
    (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown (depth + extra.length))
      value (store ++ suffix) ∧ property ⟨name, type, (store ++ suffix).length, value⟩

theorem FrameInitializersValid.extend {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References} {property : InitializedCell → Prop}
    (valid : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared property)
    (earlier : Core.Environment) (suffix : Core.Store) :
    FrameInitializersValid (depth + earlier.length) (earlier ++ environment) (store ++ suffix)
      frame dispatcher gas code codeSize codeKnown shared property := by
  intro extra later name type absent
  simpa only [List.append_assoc, List.length_append, Nat.add_assoc, Nat.add_comm earlier.length extra.length]
    using valid (extra ++ earlier) (suffix ++ later) name type absent

def RuntimeCellValid (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (name : String) (type : Core.Ty) (code : Code) (property : InitializedCell → Prop) : Prop :=
  ∃ cell : InitializedCell, cell.name = name ∧ cell.type = type ∧
    CodeValue depth environment code cell.reference ∧ store.read? cell.location = some cell.value ∧ property cell

theorem RuntimeCellValid.extend {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {name : String} {type : Core.Ty} {code : Code} {property : InitializedCell → Prop}
    (valid : RuntimeCellValid depth environment store name type code property)
    (earlier : Core.Environment) (suffix : Core.Store) :
    RuntimeCellValid (depth + earlier.length) (earlier ++ environment) (store ++ suffix) name type code property := by
  obtain ⟨cell, named, typed, related, stored, property⟩ := valid
  refine ⟨cell, named, typed, related.prepend earlier, ?_, property⟩
  have bound := (List.getElem?_eq_some_iff.mp stored).1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using stored

def FrameSharedValid (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (slots : List (String × Core.Ty)) (shared : AccountRuntime.References) (property : InitializedCell → Prop) : Prop :=
  ∀ slot ∈ slots, ∀ name code, shared.find? (·.1 == slot.1) = some (name, code) →
    RuntimeCellValid depth environment store slot.1 slot.2 code property

def FrameCreatorValid (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (slots : List (String × Core.Ty)) (creator : Code) (property : InitializedCell → Prop) : Prop :=
  ∀ type, ("createHandler", type) ∈ slots → RuntimeCellValid depth environment store "createHandler" type creator property

theorem allocateFrameSlots_validates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    {property : InitializedCell → Prop}
    (initializers : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared property)
    (sharedReady : FrameSharedValid depth environment store slots shared property)
    (creatorReady : FrameCreatorValid depth environment store slots creator property)
    {previous : List Code} {previousCells : List InitializedCell}
    (previousRelated : CodeValues depth environment previous (previousCells.map InitializedCell.reference))
    (previousStored : InitializedCells previousCells store)
    (previousValid : ∀ cell ∈ previousCells, property cell) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((previousCells.reverse ++ cells).map InitializedCell.reference) ∧
      InitializedCells (previousCells.reverse ++ cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      (∀ cell ∈ previousCells.reverse ++ cells, property cell) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrameSlots shared frame dispatcher creator gas code codeSize codeKnown
            continuation slots previous depth) result finalStore := by
  induction slots generalizing depth environment store previous previousCells with
  | nil =>
      refine ⟨[], [], previous.reverse, [], ?_, ?_, rfl, ?_, ?_⟩
      · simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil, List.map_reverse]
          using previousRelated.reverse
      · intro cell member
        simpa only [List.append_nil] using previousStored cell (by simpa using member)
      · intro cell member
        exact previousValid cell (by simpa using member)
      · intro continuation result finalStore evaluated
        simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil,
          AccountRuntime.allocateFrameSlots] using evaluated
  | cons slot rest ih =>
      rcases slot with ⟨name, type⟩
      have sharedTail : FrameSharedValid depth environment store rest shared property := by
        intro slot member
        exact sharedReady slot (.tail _ member)
      have creatorTail : FrameCreatorValid depth environment store rest creator property := by
        intro type member
        exact creatorReady type (.tail _ member)
      cases found : shared.find? (·.1 == name) with
      | some entry =>
          rcases entry with ⟨foundName, reference⟩
          obtain ⟨cell, named, typed, related, stored, valid⟩ := sharedReady (name, type) (.head _) foundName reference found
          have storedCons : InitializedCells (cell :: previousCells) store := by
            intro selected member
            cases member with
            | head => exact stored
            | tail _ member => exact previousStored selected member
          obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', evaluated⟩ :=
            ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
                (by intro selected member; cases member with
                    | head => exact valid
                    | tail _ member => exact previousValid selected member)
          refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
          · simp only [List.map_cons, named, typed, signature]
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid'
          · intro continuation result finalStore completed
            simpa only [AccountRuntime.allocateFrameSlots, found] using evaluated continuation result finalStore completed
      | none =>
          by_cases isCreator : name == "createHandler"
          · have named : name = "createHandler" := by simpa only [beq_iff_eq] using isCreator
            subst name
            obtain ⟨cell, named, typed, related, stored, valid⟩ := creatorReady type (.head _)
            have storedCons : InitializedCells (cell :: previousCells) store := by
              intro selected member
              cases member with
              | head => exact stored
              | tail _ member => exact previousStored selected member
            obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', evaluated⟩ :=
              ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
                (by intro selected member; cases member with
                    | head => exact valid
                    | tail _ member => exact previousValid selected member)
            refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_⟩
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
            · simp only [List.map_cons, named, typed, signature]
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid'
            · intro continuation result finalStore completed
              simpa only [AccountRuntime.allocateFrameSlots, found, beq_self_eq_true, ↓reduceIte]
                using evaluated continuation result finalStore completed
          · obtain ⟨value, initialized, valid⟩ := initializers [] [] name type found
            have initialized' : Core.Evaluates environment store
                (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown depth) value store := by
              simpa using initialized
            let reference : Core.Value := .cellRef type store.length
            let cell : InitializedCell := ⟨name, type, store.length, value⟩
            have sharedTail' : FrameSharedValid (depth + 1) (reference :: environment) (store ++ [value]) rest shared property := by
              intro slot member foundName foundCode found'
              simpa using (sharedTail slot member foundName foundCode found').extend [reference] [value]
            have creatorTail' : FrameCreatorValid (depth + 1) (reference :: environment) (store ++ [value]) rest creator property := by
              intro type member
              simpa using (creatorTail type member).extend [reference] [value]
            have relatedCons : CodeValues (depth + 1) (reference :: environment)
                ((fun here => .var (here - depth - 1)) :: previous) ((cell :: previousCells).map InitializedCell.reference) :=
              .cons (CodeValue.bound depth environment reference) (by simpa using previousRelated.prepend [reference])
            obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', evaluated⟩ :=
              ih (by simpa using initializers.extend [reference] [value]) sharedTail' creatorTail'
                relatedCons (previousStored.cons name type value)
                (by intro selected member; cases member with
                    | head => simpa only [List.append_nil] using valid
                    | tail _ member => exact previousValid selected member)
            refine ⟨extra ++ [reference], [value] ++ suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1, List.reverse_cons] using related'
            · simpa [List.append_assoc, List.reverse_cons] using stored'
            · exact congrArg ((name, type) :: ·) signature
            · simpa [List.append_assoc, List.reverse_cons] using valid'
            · intro continuation result finalStore completed
              simp only [AccountRuntime.allocateFrameSlots, found, isCreator]
              apply Core.Evaluates.letE (.newCell initialized')
              apply evaluated continuation result finalStore
              simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

theorem allocateFrame_memory_validates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    {property : InitializedCell → Prop}
    (initializers : FrameInitializersValid depth environment
      (store ++ [Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0)])
      frame dispatcher gas code codeSize codeKnown shared property)
    (sharedReady : FrameSharedValid depth environment store slots shared property)
    (creatorReady : FrameCreatorValid depth environment store slots creator property)
    (memoryAbsent : shared.find? (·.1 == "memory") = none)
    (sizeAbsent : shared.find? (·.1 == "memorySize") = none)
    (memoryValid : property (initialMemoryCell store)) (sizeValid : property (initialSizeCell store)) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((initialMemoryCell store :: initialSizeCell store :: cells).map InitializedCell.reference) ∧
      InitializedCells (initialMemoryCell store :: initialSizeCell store :: cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      (∀ cell ∈ initialMemoryCell store :: initialSizeCell store :: cells, property cell) ∧
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
  have sharedReady' : FrameSharedValid (depth + 2) (sizeReference :: memoryReference :: environment)
      (store ++ [memoryValue, sizeValue]) slots shared property := by
    intro slot member name code found
    simpa using (sharedReady slot member name code found).extend [sizeReference, memoryReference] [memoryValue, sizeValue]
  have creatorReady' : FrameCreatorValid (depth + 2) (sizeReference :: memoryReference :: environment)
      (store ++ [memoryValue, sizeValue]) slots creator property := by
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
  obtain ⟨extra, suffix, references, cells, related, stored, signature, valid, evaluated⟩ :=
    allocateFrameSlots_validates
      (by simpa using initializers.extend [sizeReference, memoryReference] []) sharedReady' creatorReady'
      previousRelated previousStored
      (by intro cell member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact sizeValid
          · exact memoryValid)
  have initialized : InitializedCells (initialMemoryCell store :: initialSizeCell store :: cells)
      (store ++ ([memoryValue, sizeValue] ++ suffix)) := by
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.append_assoc, List.cons_append] using stored
  refine ⟨extra ++ [sizeReference, memoryReference], [memoryValue, sizeValue] ++ suffix, references, cells,
    ?_, initialized, signature, ?_, ?_, ?_⟩
  · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 2, List.reverse_cons] using related
  · simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.append_assoc, List.cons_append] using valid
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
