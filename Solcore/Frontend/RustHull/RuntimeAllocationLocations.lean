import Solcore.Frontend.RustHull.RuntimeReferenceFacts

/-! Actual runtime allocations give differently named cells distinct locations.
Repeated references to a shared cell remain valid. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

def CellLocations (cells : List InitializedCell) : Prop :=
  ∀ left ∈ cells, ∀ right ∈ cells, left.location = right.location → left.name = right.name

theorem CellLocations.subset {cells smaller : List InitializedCell}
    (separate : CellLocations cells) (included : ∀ cell ∈ smaller, cell ∈ cells) :
    CellLocations smaller := fun left member right member' =>
  separate left (included left member) right (included right member')

theorem CellLocations.nil : CellLocations [] := by
  intro cell member
  cases member

theorem CellLocations.fresh {cells : List InitializedCell} {store : Core.Store}
    (separate : CellLocations cells) (initialized : InitializedCells cells store)
    (name : String) (type : Core.Ty) (value : Core.Value) :
    CellLocations (⟨name, type, store.length, value⟩ :: cells) := by
  intro left member right member' same
  cases member with
  | head =>
      cases member' with
      | head => rfl
      | tail _ member' =>
          have below := initialized.location_bound member'
          simp only at same
          omega
  | tail _ member =>
      cases member' with
      | head =>
          have below := initialized.location_bound member
          simp only at same
          omega
      | tail _ member' => exact separate left member right member' same

theorem CellLocations.different {cells : List InitializedCell} (separate : CellLocations cells)
    {left right : InitializedCell} (leftMember : left ∈ cells) (rightMember : right ∈ cells)
    (different : left.name ≠ right.name) : left.location ≠ right.location :=
  fun same => different (separate left leftMember right rightMember same)

theorem CellLocations.nodup {cells : List InitializedCell} (separate : CellLocations cells)
    (names : (cells.map InitializedCell.name).Nodup) :
    (cells.map InitializedCell.location).Nodup := by
  induction cells with
  | nil => exact List.nodup_nil
  | cons cell rest ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp names
      apply List.nodup_cons.mpr
      constructor
      · intro present
        obtain ⟨other, member, same⟩ := List.mem_map.mp present
        apply absent
        exact List.mem_map.mpr ⟨other, member, separate other (.tail _ member) cell (.head _) same⟩
      · exact ih (separate.subset (fun _ member => .tail _ member)) unique

theorem allocateSharedSlots_separates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {initializers : List (String × Core.Ty × Code)} {initialValues : List Core.Value}
    (inputs : CodeValues depth environment (initializers.map (·.2.2)) initialValues)
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells)
    (initialized : InitializedCells cells store)
    (separate : CellLocations cells) :
    ∃ extra suffix finalReferences finalCells,
      RuntimeReferences (depth + extra.length) (extra ++ environment) finalReferences finalCells ∧
      InitializedCells finalCells (store ++ suffix) ∧
      CellLocations finalCells ∧
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
      refine ⟨[], [], references, cells, ?_, ?_, separate, rfl, ?_⟩
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
          obtain ⟨extra, suffix, finalReferences, finalCells, finalRelated, finalInitialized, finalSeparate, description, evaluated⟩ :=
            ih (by simpa using tail.prepend [reference]) nextRelated (initialized.cons name type value) (separate.fresh initialized name type value)
          refine ⟨extra ++ [reference], [value] ++ suffix, finalReferences, finalCells, ?_, ?_, finalSeparate, ?_, ?_⟩
          · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using finalRelated
          · simpa only [List.append_assoc] using finalInitialized
          · simpa only [List.zip_cons_cons, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append, cell] using description
          · intro continuation result finalStore completed
            apply Core.Evaluates.letE (.newCell (head.evaluates store))
            apply evaluated continuation result finalStore
            simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

theorem allocateFrameSlots_separates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    {property : InitializedCell → Prop} {known : List InitializedCell}
    (initializers : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared property)
    (sharedReady : FrameSharedValid depth environment store slots shared (fun cell => property cell ∧ cell ∈ known))
    (creatorReady : FrameCreatorValid depth environment store slots creator (fun cell => property cell ∧ cell ∈ known))
    {previous : List Code} {previousCells : List InitializedCell}
    (previousRelated : CodeValues depth environment previous (previousCells.map InitializedCell.reference))
    (previousStored : InitializedCells previousCells store)
    (previousValid : ∀ cell ∈ previousCells, property cell)
    (knownStored : InitializedCells known store)
    (separate : CellLocations (known ++ previousCells)) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((previousCells.reverse ++ cells).map InitializedCell.reference) ∧
      InitializedCells (previousCells.reverse ++ cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      (∀ cell ∈ previousCells.reverse ++ cells, property cell) ∧
      CellLocations (known ++ previousCells.reverse ++ cells) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrameSlots shared frame dispatcher creator gas code codeSize codeKnown
            continuation slots previous depth) result finalStore := by
  induction slots generalizing depth environment store previous previousCells with
  | nil =>
      refine ⟨[], [], previous.reverse, [], ?_, ?_, rfl, ?_, ?_, ?_⟩
      · simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil, List.map_reverse]
          using previousRelated.reverse
      · intro cell member
        simpa only [List.append_nil] using previousStored cell (by simpa using member)
      · intro cell member
        exact previousValid cell (by simpa using member)
      · apply separate.subset
        intro cell member
        simpa only [List.mem_append, List.mem_reverse, List.not_mem_nil, or_false] using member
      · intro continuation result finalStore evaluated
        simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil,
          AccountRuntime.allocateFrameSlots] using evaluated
  | cons slot rest ih =>
      rcases slot with ⟨name, type⟩
      have sharedTail : FrameSharedValid depth environment store rest shared (fun cell => property cell ∧ cell ∈ known) := by
        intro slot member
        exact sharedReady slot (.tail _ member)
      have creatorTail : FrameCreatorValid depth environment store rest creator (fun cell => property cell ∧ cell ∈ known) := by
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
          obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', separate', evaluated⟩ :=
            ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
                (by intro selected member; cases member with
                    | head => exact valid.1
                    | tail _ member => exact previousValid selected member) knownStored
                (by
                  apply separate.subset
                  intro selected member
                  simp only [List.mem_append, List.mem_cons] at member ⊢
                  rcases member with old | rfl | previous
                  · exact Or.inl old
                  · exact Or.inl valid.2
                  · exact Or.inr previous)
          refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
          · simp only [List.map_cons, named, typed, signature]
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid'
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using separate'
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
            obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', separate', evaluated⟩ :=
              ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
                (by intro selected member; cases member with
                    | head => exact valid.1
                    | tail _ member => exact previousValid selected member) knownStored
                (by
                  apply separate.subset
                  intro selected member
                  simp only [List.mem_append, List.mem_cons] at member ⊢
                  rcases member with old | rfl | previous
                  · exact Or.inl old
                  · exact Or.inl valid.2
                  · exact Or.inr previous)
            refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
            · simp only [List.map_cons, named, typed, signature]
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid'
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using separate'
            · intro continuation result finalStore completed
              simpa only [AccountRuntime.allocateFrameSlots, found, beq_self_eq_true, ↓reduceIte]
                using evaluated continuation result finalStore completed
          · obtain ⟨value, initialized, valid⟩ := initializers [] [] name type found
            have initialized' : Core.Evaluates environment store
                (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown depth) value store := by
              simpa using initialized
            let reference : Core.Value := .cellRef type store.length
            let cell : InitializedCell := ⟨name, type, store.length, value⟩
            have sharedTail' : FrameSharedValid (depth + 1) (reference :: environment) (store ++ [value]) rest shared
                (fun cell => property cell ∧ cell ∈ known) := by
              intro slot member foundName foundCode found'
              simpa using (sharedTail slot member foundName foundCode found').extend [reference] [value]
            have creatorTail' : FrameCreatorValid (depth + 1) (reference :: environment) (store ++ [value]) rest creator
                (fun cell => property cell ∧ cell ∈ known) := by
              intro type member
              simpa using (creatorTail type member).extend [reference] [value]
            have relatedCons : CodeValues (depth + 1) (reference :: environment)
                ((fun here => .var (here - depth - 1)) :: previous) ((cell :: previousCells).map InitializedCell.reference) :=
              .cons (CodeValue.bound depth environment reference) (by simpa using previousRelated.prepend [reference])
            obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', separate', evaluated⟩ :=
              ih (by simpa using initializers.extend [reference] [value]) sharedTail' creatorTail'
                relatedCons (previousStored.cons name type value)
                (by intro selected member; cases member with
                    | head => simpa only [List.append_nil] using valid
                    | tail _ member => exact previousValid selected member)
                (knownStored.appendStore [value])
                (by
                  have allStored : InitializedCells (known ++ previousCells) store := by
                    intro selected member
                    rcases List.mem_append.mp member with old | previous
                    · exact knownStored selected old
                    · exact previousStored selected previous
                  apply (separate.fresh allStored name type value).subset
                  intro selected member
                  simp only [List.mem_append, List.mem_cons] at member ⊢
                  rcases member with old | rfl | previous
                  · exact Or.inr (Or.inl old)
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr previous))
            refine ⟨extra ++ [reference], [value] ++ suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1, List.reverse_cons] using related'
            · simpa [List.append_assoc, List.reverse_cons] using stored'
            · exact congrArg ((name, type) :: ·) signature
            · simpa [List.append_assoc, List.reverse_cons] using valid'
            · simpa [List.append_assoc, List.reverse_cons] using separate'
            · intro continuation result finalStore completed
              simp only [AccountRuntime.allocateFrameSlots, found, isCreator]
              apply Core.Evaluates.letE (.newCell initialized')
              apply evaluated continuation result finalStore
              simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

end Solcore.Frontend.RustHull.Correspondence
