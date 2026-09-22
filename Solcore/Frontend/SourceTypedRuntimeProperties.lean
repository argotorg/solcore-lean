import Solcore.Frontend.SourceTypedRuntime

/-!
Small executable contracts for the phase-7 typed-source runtime.

The phase intentionally prioritizes a complete running language slice over a
large metatheory.  These lemmas nevertheless pin down the public fuel boundary,
the successful-result projection, and representative deep-value validation
rules used at the safe input boundary.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem

@[simp] theorem Cell.hasShallowType_none (plan : Plan) (type : Ty) :
    ({ type, value := none } : Cell).HasShallowType plan := by
  intro value impossible
  cases impossible

theorem Cell.hasShallowType_some
    (plan : Plan) (type : Ty) (value : Value)
    (typed : value.type? plan = some type) :
    ({ type, value := some value } : Cell).HasShallowType plan := by
  intro selected equal
  cases equal
  exact typed

@[simp] theorem RuntimeState.hasShallowTypes_empty (plan : Plan) :
    ({} : RuntimeState).HasShallowTypes plan := by
  intro cell member
  simp at member

theorem RuntimeState.HasShallowTypes.read
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {cell : Cell}
    (found : state.read? location = some cell) :
    cell.HasShallowType plan := by
  apply typing cell
  exact List.mem_of_getElem? (by
    simpa [RuntimeState.read?] using found)

/-- Reading an initialized cell from a shallow-typed heap yields a value with
the cell's declared type. -/
theorem RuntimeState.HasShallowTypes.read_value
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {cell : Cell} {value : Value}
    (found : state.read? location = some cell)
    (initialized : cell.value = some value) :
    value.type? plan = some cell.type :=
  (typing.read found) value initialized

theorem RuntimeState.HasShallowTypes.allocate
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) (value : Option Value)
    (fresh : ({ type, value } : Cell).HasShallowType plan) :
    (state.allocate type value).2.HasShallowTypes plan := by
  intro selected member
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | appended
  · exact typing selected old
  · simp only [List.mem_singleton] at appended
    subst selected
    exact fresh

theorem RuntimeState.HasShallowTypes.allocate_none
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) :
    (state.allocate type none).2.HasShallowTypes plan :=
  typing.allocate type none (Cell.hasShallowType_none plan type)

theorem RuntimeState.HasShallowTypes.allocate_some
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) (value : Value)
    (typed : value.type? plan = some type) :
    (state.allocate type (some value)).2.HasShallowTypes plan :=
  typing.allocate type (some value)
    (Cell.hasShallowType_some plan type value typed)

theorem RuntimeState.HasShallowTypes.write?_none
    {plan : Plan} {state updated : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {previous : Cell}
    (found : state.read? location = some previous)
    (written : state.write? location none = some updated) :
    updated.HasShallowTypes plan := by
  apply typing.write? found _ written
  intro value impossible
  cases impossible

theorem RuntimeState.HasShallowTypes.write?_some
    {plan : Plan} {state updated : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (typed : value.type? plan = some previous.type)
    (written : state.write? location (some value) = some updated) :
    updated.HasShallowTypes plan := by
  apply typing.write? found _ written
  intro selected equal
  cases equal
  exact typed

/-- Any positive deep observation includes the outer runtime type tag. -/
theorem Value.HasDeepTypeFuel.shallow
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {expected : Ty} {value : Value}
    (typed : value.HasDeepTypeFuel (fuel + 1) signatures plan state expected) :
    value.type? plan = some expected :=
  typed.1

/-- Deep heap typing refines the existing shallow heap invariant. -/
theorem RuntimeState.HasDeepTypesFuel.shallow
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (typing : state.HasDeepTypesFuel (fuel + 1) signatures plan) :
    state.HasShallowTypes plan := by
  intro cell member value initialized
  exact (typing cell member value initialized).shallow

theorem RuntimeState.HasDeepTypes.shallow
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    (typing : state.HasDeepTypes signatures plan) :
    state.HasShallowTypes plan :=
  (typing 1).shallow

@[simp] theorem RuntimeState.hasDeepTypes_empty
    (signatures : ProgramSignatures) (plan : Plan) :
    ({} : RuntimeState).HasDeepTypes signatures plan := by
  intro fuel cell member
  simp at member

theorem RuntimeState.HasDeepTypes.read_value
    {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (typing : state.HasDeepTypes signatures plan)
    {location : Location} {cell : Cell} {value : Value}
    (found : state.read? location = some cell)
    (initialized : cell.value = some value) :
    value.HasDeepType signatures plan state cell.type := by
  intro fuel
  apply typing fuel cell
  · exact List.mem_of_getElem? (by
      simpa [RuntimeState.read?] using found)
  · exact initialized

/-- Deep typing excludes self-consistent but unauthorized nominal constructor
metadata, in addition to checking each paired payload recursively. -/
theorem Value.HasDeepTypeFuel.constructed_authorized
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {expected : Ty}
    {instantiation : DataConstructorInstantiation} {arguments : List Value}
    (typed : (Value.constructed instantiation arguments).HasDeepTypeFuel
      (fuel + 1) signatures plan state expected) :
    validConstructorInstantiation signatures instantiation = true :=
  typed.2.2.1

theorem Value.HasDeepTypeFuel.mapping_entry
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {keyType valueType : Ty}
    {entries : List (Value × Value)} {entry : Value × Value}
    (typed : (Value.mapping keyType valueType entries).HasDeepTypeFuel
      (fuel + 1) signatures plan state (.mapping keyType valueType))
    (member : entry ∈ entries) :
    entry.1.HasDeepTypeFuel fuel signatures plan state keyType ∧
      entry.2.HasDeepTypeFuel fuel signatures plan state valueType :=
  typed.2.2.2 entry member

theorem Value.HasDeepTypeFuel.closure_captured
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {parameters : List TypedBinder}
    {resultType : Ty} {body : List StatementId} {source : TypedSource}
    {owner : Key} {captured : Environment}
    {binding : Resolved.LocalId × Location}
    (typed : (Value.closure parameters resultType body source owner captured).HasDeepTypeFuel
      (fuel + 1) signatures plan state
        (.function (Ty.productMany (parameters.map (·.scheme.body))) resultType))
    (member : binding ∈ captured) :
    ∃ cell, state.read? binding.2 = some cell ∧
      cell.HasDeepTypeFuel fuel signatures plan state :=
  typed.2.2 binding member

/-- Inspecting one fewer layer never invalidates deep typing. -/
theorem Value.HasDeepTypeFuel.down
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState} :
    ∀ (fuel : Nat) (expected : Ty) (value : Value),
      value.HasDeepTypeFuel (fuel + 1) signatures plan state expected →
        value.HasDeepTypeFuel fuel signatures plan state expected := by
  intro fuel
  induction fuel with
  | zero =>
      intro expected value _
      trivial
  | succ fuel inductionHypothesis =>
      intro expected value typed
      cases value with
      | product left right =>
          cases expected <;> try exact False.elim typed.2
          case product leftType rightType =>
            exact ⟨typed.1,
              inductionHypothesis leftType left typed.2.1,
              inductionHypothesis rightType right typed.2.2⟩
      | mapping actualKey actualValue entries =>
          cases expected <;> try exact False.elim typed.2
          case mapping keyType valueType =>
            exact ⟨typed.1, typed.2.1, typed.2.2.1,
              fun entry member =>
                ⟨inductionHypothesis keyType entry.1
                    (typed.2.2.2 entry member).1,
                  inductionHypothesis valueType entry.2
                    (typed.2.2.2 entry member).2⟩⟩
      | constructed instantiation arguments =>
          exact ⟨typed.1, typed.2.1, typed.2.2.1, typed.2.2.2.1,
            fun pair member =>
              inductionHypothesis pair.1 pair.2
                (typed.2.2.2.2 pair member)⟩
      | closure parameters resultType body source owner captured =>
          exact ⟨typed.1, typed.2.1,
            fun binding member => by
              obtain ⟨cell, found, cellTyped⟩ := typed.2.2 binding member
              exact ⟨cell, found,
                fun capturedValue initialized =>
                  inductionHypothesis cell.type capturedValue
                    (cellTyped capturedValue initialized)⟩⟩
      | unit => exact typed
      | bool _ => exact typed
      | word _ => exact typed
      | integer _ => exact typed
      | proxy _ => exact typed
      | global _ => exact typed
      | builtin _ => exact typed

theorem RuntimeState.HasDeepTypesFuel.down
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (typing : state.HasDeepTypesFuel (fuel + 1) signatures plan) :
    state.HasDeepTypesFuel fuel signatures plan := by
  intro cell member value initialized
  exact Value.HasDeepTypeFuel.down fuel cell.type value
    (typing cell member value initialized)

/-- A readable initialized cell inherits deep typing from the heap world. -/
theorem RuntimeState.HasDeepTypesFuel.read_value
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (typing : state.HasDeepTypesFuel fuel signatures plan)
    {location : Location} {cell : Cell} {value : Value}
    (found : state.read? location = some cell)
    (initialized : cell.value = some value) :
    value.HasDeepTypeFuel fuel signatures plan state cell.type := by
  apply typing cell
  · exact List.mem_of_getElem? (by
      simpa [RuntimeState.read?] using found)
  · exact initialized

/-- Deep values remain typed when every location they can observe continues
to read the same cell.  This forward form handles heap extension, including
closures that capture locations in the old prefix. -/
theorem Value.HasDeepTypeFuel.transport_world
    {signatures : ProgramSignatures} {plan : Plan}
    {oldWorld newWorld : RuntimeState}
    (preserved : ∀ location cell,
      oldWorld.read? location = some cell →
        newWorld.read? location = some cell) :
    ∀ (fuel : Nat) (expected : Ty) (value : Value),
      value.HasDeepTypeFuel fuel signatures plan oldWorld expected →
        value.HasDeepTypeFuel fuel signatures plan newWorld expected := by
  intro fuel
  induction fuel with
  | zero =>
      intro expected value _
      trivial
  | succ fuel inductionHypothesis =>
      intro expected value typed
      cases value with
      | product left right =>
          cases expected <;> try exact False.elim typed.2
          case product leftType rightType =>
            exact ⟨typed.1,
              inductionHypothesis leftType left typed.2.1,
              inductionHypothesis rightType right typed.2.2⟩
      | mapping actualKey actualValue entries =>
          cases expected <;> try exact False.elim typed.2
          case mapping keyType valueType =>
            exact ⟨typed.1, typed.2.1, typed.2.2.1,
              fun entry member =>
                ⟨inductionHypothesis keyType entry.1
                    (typed.2.2.2 entry member).1,
                  inductionHypothesis valueType entry.2
                    (typed.2.2.2 entry member).2⟩⟩
      | constructed instantiation arguments =>
          exact ⟨typed.1, typed.2.1, typed.2.2.1, typed.2.2.2.1,
            fun pair member =>
              inductionHypothesis pair.1 pair.2
                (typed.2.2.2.2 pair member)⟩
      | closure parameters resultType body source owner captured =>
          exact ⟨typed.1, typed.2.1,
            fun binding member => by
              obtain ⟨cell, found, cellTyped⟩ := typed.2.2 binding member
              exact ⟨cell, preserved binding.2 cell found,
                fun capturedValue initialized =>
                  inductionHypothesis cell.type capturedValue
                    (cellTyped capturedValue initialized)⟩⟩
      | unit => exact typed
      | bool _ => exact typed
      | word _ => exact typed
      | integer _ => exact typed
      | proxy _ => exact typed
      | global _ => exact typed
      | builtin _ => exact typed

theorem Value.HasDeepType.transport_world
    {signatures : ProgramSignatures} {plan : Plan}
    {oldWorld newWorld : RuntimeState} {expected : Ty} {value : Value}
    (preserved : ∀ location cell,
      oldWorld.read? location = some cell →
        newWorld.read? location = some cell)
    (typed : value.HasDeepType signatures plan oldWorld expected) :
    value.HasDeepType signatures plan newWorld expected := by
  intro fuel
  exact Value.HasDeepTypeFuel.transport_world preserved fuel expected value
    (typed fuel)

/-- An old value remains deep in a new well-typed world when each location it
could have captured still exists with the same declared type.  At closure
nodes, the new heap invariant supplies the captured cell's new contents. -/
theorem Value.HasDeepTypeFuel.transport_typed_world
    {signatures : ProgramSignatures} {plan : Plan}
    {oldWorld newWorld : RuntimeState}
    (preservedTypes : ∀ location oldCell,
      oldWorld.read? location = some oldCell →
        ∃ newCell, newWorld.read? location = some newCell ∧
          newCell.type = oldCell.type) :
    ∀ (fuel : Nat) (expected : Ty) (value : Value),
      newWorld.HasDeepTypesFuel fuel signatures plan →
      value.HasDeepTypeFuel (fuel + 1) signatures plan oldWorld expected →
        value.HasDeepTypeFuel (fuel + 1) signatures plan newWorld expected := by
  intro fuel
  induction fuel with
  | zero =>
      intro expected value newTyping typed
      cases value with
      | closure parameters resultType body source owner captured =>
          exact ⟨typed.1, typed.2.1,
            fun binding member => by
              obtain ⟨oldCell, found, _⟩ := typed.2.2 binding member
              obtain ⟨newCell, newFound, _⟩ :=
                preservedTypes binding.2 oldCell found
              exact ⟨newCell, newFound, fun _ _ => trivial⟩⟩
      | product _ _ => exact typed
      | mapping _ _ _ => exact typed
      | constructed _ _ => exact typed
      | unit => exact typed
      | bool _ => exact typed
      | word _ => exact typed
      | integer _ => exact typed
      | proxy _ => exact typed
      | global _ => exact typed
      | builtin _ => exact typed
  | succ fuel inductionHypothesis =>
      intro expected value newTyping typed
      cases value with
      | product left right =>
          cases expected <;> try exact False.elim typed.2
          case product leftType rightType =>
            exact ⟨typed.1,
              inductionHypothesis leftType left newTyping.down typed.2.1,
              inductionHypothesis rightType right newTyping.down typed.2.2⟩
      | mapping actualKey actualValue entries =>
          cases expected <;> try exact False.elim typed.2
          case mapping keyType valueType =>
            exact ⟨typed.1, typed.2.1, typed.2.2.1,
              fun entry member =>
                ⟨inductionHypothesis keyType entry.1 newTyping.down
                    (typed.2.2.2 entry member).1,
                  inductionHypothesis valueType entry.2 newTyping.down
                    (typed.2.2.2 entry member).2⟩⟩
      | constructed instantiation arguments =>
          exact ⟨typed.1, typed.2.1, typed.2.2.1, typed.2.2.2.1,
            fun pair member =>
              inductionHypothesis pair.1 pair.2 newTyping.down
                (typed.2.2.2.2 pair member)⟩
      | closure parameters resultType body source owner captured =>
          exact ⟨typed.1, typed.2.1,
            fun binding member => by
              obtain ⟨oldCell, found, _⟩ := typed.2.2 binding member
              obtain ⟨newCell, newFound, sameType⟩ :=
                preservedTypes binding.2 oldCell found
              exact ⟨newCell, newFound, fun capturedValue initialized => by
                have typedNew : capturedValue.HasDeepTypeFuel (fuel + 1)
                    signatures plan newWorld newCell.type :=
                  newTyping.read_value newFound initialized
                exact sameType ▸ typedNew⟩⟩
      | unit => exact typed
      | bool _ => exact typed
      | word _ => exact typed
      | integer _ => exact typed
      | proxy _ => exact typed
      | global _ => exact typed
      | builtin _ => exact typed

/-- Appending a fresh cell does not alter reads of already allocated cells. -/
theorem RuntimeState.read?_allocate_old
    (state : RuntimeState) (type : Ty) (value : Option Value)
    (location : Location) (cell : Cell)
    (found : state.read? location = some cell) :
    (state.allocate type value).2.read? location = some cell := by
  by_cases indexValid : location.index < state.heap.length
  · simpa [RuntimeState.read?, RuntimeState.allocate, List.getElem?_append,
      indexValid] using found
  ·
    have empty : state.heap[location.index]? = none := by
      simp [Nat.le_of_not_lt indexValid]
    simp [RuntimeState.read?, empty] at found

/-- Allocation preserves the self-consistent deep heap invariant when the new
value is deeply typed in the old heap.  Captured closure locations remain
valid because allocation only extends the heap. -/
theorem RuntimeState.HasDeepTypes.allocate_some
    {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} (typing : state.HasDeepTypes signatures plan)
    (type : Ty) (value : Value)
    (deep : value.HasDeepType signatures plan state type) :
    (state.allocate type (some value)).2.HasDeepTypes signatures plan := by
  intro fuel selected member actual initialized
  have preserved : ∀ location cell,
      state.read? location = some cell →
        (state.allocate type (some value)).2.read? location = some cell := by
    intro location cell found
    exact RuntimeState.read?_allocate_old state type (some value)
      location cell found
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact Value.HasDeepTypeFuel.transport_world preserved fuel selected.type
      actual (typing fuel selected old actual initialized)
  · simp only [List.mem_singleton] at fresh
    subst selected
    cases initialized
    exact Value.HasDeepTypeFuel.transport_world preserved fuel type value
      (deep fuel)

theorem RuntimeState.HasDeepTypes.allocate_none
    {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} (typing : state.HasDeepTypes signatures plan)
    (type : Ty) :
    (state.allocate type none).2.HasDeepTypes signatures plan := by
  intro fuel selected member actual initialized
  have preserved : ∀ location cell,
      state.read? location = some cell →
        (state.allocate type none).2.read? location = some cell := by
    intro location cell found
    exact RuntimeState.read?_allocate_old state type none location cell found
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact Value.HasDeepTypeFuel.transport_world preserved fuel selected.type
      actual (typing fuel selected old actual initialized)
  · simp only [List.mem_singleton] at fresh
    subst selected
    cases initialized

/-- Parameter and pattern binding in the actual evaluator preserves deep heap
typing, provided every supplied value is deeply typed in the entry state.
Heap extension transports the remaining values' captured locations. -/
theorem bindValues_ok_preserves_deep_types
    (signatures : ProgramSignatures) (plan : Plan)
    (bindings : List (TypedBinder × Value))
    (environment finalEnvironment : Environment)
    (state finalState : RuntimeState)
    (typing : state.HasDeepTypes signatures plan)
    (inputs : ∀ binding, binding ∈ bindings →
      binding.2.HasDeepType signatures plan state binding.1.scheme.body)
    (bound : bindValues plan environment state bindings =
      .ok (finalEnvironment, finalState)) :
    finalState.HasDeepTypes signatures plan := by
  induction bindings generalizing environment state with
  | nil =>
      simp [bindValues] at bound
      obtain ⟨rfl, rfl⟩ := bound
      exact typing
  | cons binding rest inductionHypothesis =>
      obtain ⟨binder, value⟩ := binding
      have valueDeep : value.HasDeepType signatures plan state binder.scheme.body :=
        inputs (binder, value) (List.Mem.head rest)
      have valueType : value.type? plan = some binder.scheme.body :=
        (valueDeep 1).shallow
      simp [bindValues, valueType, bne] at bound
      let nextState := (state.allocate binder.scheme.body (some value)).2
      have nextTyping : nextState.HasDeepTypes signatures plan :=
        typing.allocate_some binder.scheme.body value valueDeep
      have nextInputs : ∀ pair, pair ∈ rest →
          pair.2.HasDeepType signatures plan nextState pair.1.scheme.body := by
        intro pair member
        apply Value.HasDeepType.transport_world
        · intro location cell found
          exact RuntimeState.read?_allocate_old state binder.scheme.body
            (some value) location cell found
        · exact inputs pair (List.Mem.tail (binder, value) member)
      exact inductionHypothesis _ _ nextTyping nextInputs bound

/-- Writing a deeply typed cell preserves heap typing relative to a fixed
reference world.  Moving that world to the updated heap additionally requires
the world-transport theorem proved below. -/
theorem RuntimeState.HasDeepTypesAtFuel.write?_some
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state updated world : RuntimeState}
    (typing : state.HasDeepTypesAtFuel world fuel signatures plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (deep : value.HasDeepTypeFuel fuel signatures plan world previous.type)
    (written : state.write? location (some value) = some updated) :
    updated.HasDeepTypesAtFuel world fuel signatures plan := by
  unfold RuntimeState.write? at written
  rw [found] at written
  cases written
  intro selected member
  rcases RuntimeState.mem_replaceCell location.index
      { previous with value := some value } selected state.heap member with
    replaced | old
  · subst selected
    intro actual initialized
    cases initialized
    exact deep
  · exact typing selected old

/-- Every previously readable location remains readable with the same cell
annotation after a successful write.  The optional value may change. -/
theorem RuntimeState.write?_preserves_read_types
    {state updated : RuntimeState} {target : Location}
    {value : Option Value}
    (written : state.write? target value = some updated) :
    ∀ location oldCell,
      state.read? location = some oldCell →
        ∃ newCell, updated.read? location = some newCell ∧
          newCell.type = oldCell.type := by
  intro location oldCell found
  have sameTypes := RuntimeState.write?_typeVector_eq state updated target value
    written
  have oldType : (state.heap.map Cell.type)[location.index]? =
      some oldCell.type := by
    simpa [RuntimeState.read?] using congrArg (Option.map Cell.type) found
  rw [← sameTypes] at oldType
  cases newRead : updated.read? location with
  | none =>
      have noType : (updated.heap.map Cell.type)[location.index]? = none := by
        simpa [RuntimeState.read?] using
          congrArg (Option.map Cell.type) newRead
      rw [noType] at oldType
      cases oldType
  | some newCell =>
      have newType : (updated.heap.map Cell.type)[location.index]? =
          some newCell.type := by
        simpa [RuntimeState.read?] using
          congrArg (Option.map Cell.type) newRead
      rw [newType] at oldType
      exact ⟨newCell, rfl, Option.some.inj oldType⟩

/-- A same-annotation write preserves deep *structural heap* typing when the
replacement is deeply typed in the resulting heap world.  The induction on
observation depth accounts for closures that capture the changed location. -/
theorem RuntimeState.HasDeepTypes.write?_some
    {signatures : ProgramSignatures} {plan : Plan}
    {state updated : RuntimeState}
    (typing : state.HasDeepTypes signatures plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (written : state.write? location (some value) = some updated)
    (deep : value.HasDeepType signatures plan updated previous.type) :
    updated.HasDeepTypes signatures plan := by
  intro fuel
  induction fuel with
  | zero =>
      intro cell member actual initialized
      trivial
  | succ fuel inductionHypothesis =>
      have oldAtNewWorld : state.HasDeepTypesAtFuel updated (fuel + 1)
          signatures plan := by
        intro cell member actual initialized
        exact Value.HasDeepTypeFuel.transport_typed_world
          (RuntimeState.write?_preserves_read_types written)
          fuel cell.type actual inductionHypothesis
          (typing (fuel + 1) cell member actual initialized)
      exact oldAtNewWorld.write?_some found (deep (fuel + 1)) written

@[simp] theorem RuntimeState.hasPlanCodes_empty (plan : Plan) :
    ({} : RuntimeState).HasPlanCodes plan := by
  intro cell member
  simp at member

theorem RuntimeState.HasPlanCodes.allocate_none
    {plan : Plan} {state : RuntimeState}
    (typing : state.HasPlanCodes plan) (type : Ty) :
    (state.allocate type none).2.HasPlanCodes plan := by
  intro cell member value initialized
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact typing cell old value initialized
  · simp only [List.mem_singleton] at fresh
    subst cell
    cases initialized

theorem RuntimeState.HasPlanCodes.allocate_some
    {plan : Plan} {state : RuntimeState}
    (typing : state.HasPlanCodes plan) (type : Ty) (value : Value)
    (code : value.HasPlanCode plan) :
    (state.allocate type (some value)).2.HasPlanCodes plan := by
  intro cell member actual initialized
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact typing cell old actual initialized
  · simp only [List.mem_singleton] at fresh
    subst cell
    cases initialized
    exact code

theorem RuntimeState.HasPlanCodes.write?_some
    {plan : Plan} {state updated : RuntimeState}
    (typing : state.HasPlanCodes plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (code : value.HasPlanCode plan)
    (written : state.write? location (some value) = some updated) :
    updated.HasPlanCodes plan := by
  unfold RuntimeState.write? at written
  rw [found] at written
  cases written
  intro selected member actual initialized
  rcases RuntimeState.mem_replaceCell location.index
      { previous with value := some value } selected state.heap member with
    replaced | old
  · subst selected
    cases initialized
    exact code
  · exact typing selected old actual initialized

/-- The exact structural-update obligation required for a successful place
write.  The leaf `modify` callback alone does not imply this contract: the
recursive updater must also preserve deep typing and code provenance of every
unmodified mapping entry or constructor field. -/
def ResolvedPlace.UpdatePreservesDeepAndCode
    (signatures : ProgramSignatures) (plan : Plan) (state : RuntimeState)
    (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value) : Prop :=
  ∀ cell updated finalState,
    state.read? place.location = some cell →
    cell.type = place.rootType →
    updateResolvedValue plan place.valueType modify
      (initialRootValue cell) place.projections = .ok updated →
    updated.type? plan = some place.rootType →
    state.write? place.location (some updated) = some finalState →
    updated.HasDeepType signatures plan finalState place.rootType ∧
      updated.HasPlanCode plan

/-- A present mapping-key projection reconstructs exactly one mapping after
the recursive child update. -/
theorem updateResolvedValue_index_present_eq
    (plan : Plan) (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child : Value) (entries : List (Value × Value))
    (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (found : mappingLookup? key entries = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child) :
    updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
      .ok (.mapping keyType valueType
        (mappingInsert key child entries)) := by
  simp [updateResolvedValue, keyTyped, bne, found, recursive]
  rfl

/-- When a missing mapping key has a runtime default, that default is the
recursive child; the same mapping frame is reconstructed afterward. -/
theorem updateResolvedValue_index_default_eq
    (plan : Plan) (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child : Value) (entries : List (Value × Value))
    (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (missing : mappingLookup? key entries = none)
    (defaulted : defaultValue? (valueType.size + 1) valueType = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child) :
    updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
      .ok (.mapping keyType valueType
        (mappingInsert key child entries)) := by
  simp [updateResolvedValue, keyTyped, bne, missing, defaulted, recursive]
  rfl

/-- A constructor member projection replaces exactly the selected payload
slot after the recursive child update. -/
theorem updateResolvedValue_member_eq
    (plan : Plan) (expected : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (name : String) (index : Nat) (selected child : Value)
    (rest : List RuntimeProjection)
    (found : arguments[index]? = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (replacement : replaceValueAt index child arguments = some replaced) :
    updateResolvedValue plan expected modify
      (some (.constructed instantiation arguments))
      (.member name index :: rest) =
      .ok (.constructed instantiation replaced) := by
  simp [updateResolvedValue, found, recursive]
  change (match replaceValueAt index child arguments with
    | some arguments => Except.ok (Value.constructed instantiation arguments)
    | none => Except.error (RuntimeError.invalidMember name index
        ((Value.constructed instantiation arguments).type? plan))) =
      Except.ok (Value.constructed instantiation replaced)
  rw [replacement]

/-- Mapping projection preserves the deep structural and code-provenance
properties when the recursive child and the local mapping frame do. -/
theorem updateResolvedValue_index_present_preserves
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child updated : Value)
    (entries : List (Value × Value)) (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (found : mappingLookup? key entries = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (childDeep : child.HasDeepType signatures plan world valueType)
    (childCode : child.HasPlanCode plan)
    (frame : ∀ replacement,
      replacement.HasDeepType signatures plan world valueType →
      replacement.HasPlanCode plan →
      (Value.mapping keyType valueType
        (mappingInsert key replacement entries)).HasDeepType
          signatures plan world (.mapping keyType valueType) ∧
      (Value.mapping keyType valueType
        (mappingInsert key replacement entries)).HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
        .ok updated) :
    updated.HasDeepType signatures plan world (.mapping keyType valueType) ∧
      updated.HasPlanCode plan := by
  rw [updateResolvedValue_index_present_eq plan expected keyType valueType
    modify key selected child entries rest keyTyped found recursive] at done
  cases done
  exact frame child childDeep childCode

theorem updateResolvedValue_index_default_preserves
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child updated : Value)
    (entries : List (Value × Value)) (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (missing : mappingLookup? key entries = none)
    (defaulted : defaultValue? (valueType.size + 1) valueType = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (childDeep : child.HasDeepType signatures plan world valueType)
    (childCode : child.HasPlanCode plan)
    (frame : ∀ replacement,
      replacement.HasDeepType signatures plan world valueType →
      replacement.HasPlanCode plan →
      (Value.mapping keyType valueType
        (mappingInsert key replacement entries)).HasDeepType
          signatures plan world (.mapping keyType valueType) ∧
      (Value.mapping keyType valueType
        (mappingInsert key replacement entries)).HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
        .ok updated) :
    updated.HasDeepType signatures plan world (.mapping keyType valueType) ∧
      updated.HasPlanCode plan := by
  rw [updateResolvedValue_index_default_eq plan expected keyType valueType
    modify key selected child entries rest keyTyped missing defaulted recursive]
    at done
  cases done
  exact frame child childDeep childCode

/-- Mapping insertion is a genuine deep structural frame operation: old
entries keep their typing and code provenance, while the new entry uses the
explicit key and replacement witnesses. -/
theorem Value.mappingInsert_hasDeepType
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (keyType valueType : Ty) (entries : List (Value × Value))
    (key replacement : Value)
    (old : (Value.mapping keyType valueType entries).HasDeepType
      signatures plan world (.mapping keyType valueType))
    (keyDeep : key.HasDeepType signatures plan world keyType)
    (replacementDeep : replacement.HasDeepType signatures plan world valueType) :
    (Value.mapping keyType valueType
      (mappingInsert key replacement entries)).HasDeepType
        signatures plan world (.mapping keyType valueType) := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro entry member
      rcases mappingInsert_member key replacement entries entry member with
        fresh | retained
      · subst entry
        exact ⟨keyDeep fuel, replacementDeep fuel⟩
      · exact (old (fuel + 1)).2.2.2 entry retained

theorem Value.mappingInsert_hasPlanCode
    (plan : Plan) (keyType valueType : Ty)
    (entries : List (Value × Value)) (key replacement : Value)
    (old : (Value.mapping keyType valueType entries).HasPlanCode plan)
    (keyCode : key.HasPlanCode plan)
    (replacementCode : replacement.HasPlanCode plan) :
    (Value.mapping keyType valueType
      (mappingInsert key replacement entries)).HasPlanCode plan := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      intro entry member
      rcases mappingInsert_member key replacement entries entry member with
        fresh | retained
      · subst entry
        exact ⟨keyCode fuel, replacementCode fuel⟩
      · exact old (fuel + 1) entry retained

/-- The mapping default constructed for an uninitialized mapping or a fresh
mapping-typed slot has both structural and code-provenance witnesses. -/
theorem Value.emptyMapping_hasDeepType
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (keyType valueType : Ty) :
    (Value.mapping keyType valueType []).HasDeepType signatures plan world
      (.mapping keyType valueType) := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro entry member
      cases member

theorem Value.emptyMapping_hasPlanCode
    (plan : Plan) (keyType valueType : Ty) :
    (Value.mapping keyType valueType []).HasPlanCode plan := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      intro entry member
      cases member

/-- The present-key path needs no abstract mapping frame premise once its
existing mapping, key, and updated child are deeply typed. -/
theorem updateResolvedValue_index_present_preserves_from_parts
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child updated : Value)
    (entries : List (Value × Value)) (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (found : mappingLookup? key entries = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (oldDeep : (Value.mapping keyType valueType entries).HasDeepType
      signatures plan world (.mapping keyType valueType))
    (oldCode : (Value.mapping keyType valueType entries).HasPlanCode plan)
    (keyDeep : key.HasDeepType signatures plan world keyType)
    (keyCode : key.HasPlanCode plan)
    (childDeep : child.HasDeepType signatures plan world valueType)
    (childCode : child.HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
        .ok updated) :
    updated.HasDeepType signatures plan world (.mapping keyType valueType) ∧
      updated.HasPlanCode plan := by
  apply updateResolvedValue_index_present_preserves signatures plan world
    expected keyType valueType modify key selected child updated entries rest
    keyTyped found recursive childDeep childCode
  · intro replacement replacementDeep replacementCode
    exact ⟨Value.mappingInsert_hasDeepType signatures plan world keyType
        valueType entries key replacement oldDeep keyDeep replacementDeep,
      Value.mappingInsert_hasPlanCode plan keyType valueType entries key
        replacement oldCode keyCode replacementCode⟩
  · exact done

theorem updateResolvedValue_index_default_preserves_from_parts
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child updated : Value)
    (entries : List (Value × Value)) (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (missing : mappingLookup? key entries = none)
    (defaulted : defaultValue? (valueType.size + 1) valueType = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (oldDeep : (Value.mapping keyType valueType entries).HasDeepType
      signatures plan world (.mapping keyType valueType))
    (oldCode : (Value.mapping keyType valueType entries).HasPlanCode plan)
    (keyDeep : key.HasDeepType signatures plan world keyType)
    (keyCode : key.HasPlanCode plan)
    (childDeep : child.HasDeepType signatures plan world valueType)
    (childCode : child.HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
        .ok updated) :
    updated.HasDeepType signatures plan world (.mapping keyType valueType) ∧
      updated.HasPlanCode plan := by
  apply updateResolvedValue_index_default_preserves signatures plan world
    expected keyType valueType modify key selected child updated entries rest
    keyTyped missing defaulted recursive childDeep childCode
  · intro replacement replacementDeep replacementCode
    exact ⟨Value.mappingInsert_hasDeepType signatures plan world keyType
        valueType entries key replacement oldDeep keyDeep replacementDeep,
      Value.mappingInsert_hasPlanCode plan keyType valueType entries key
        replacement oldCode keyCode replacementCode⟩
  · exact done

/-- A constructor member projection preserves the invariants when replacing
the chosen payload field is a valid local frame operation. -/
theorem updateResolvedValue_member_preserves
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected fieldType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (name : String) (index : Nat)
    (selected child updated : Value) (rest : List RuntimeProjection)
    (found : arguments[index]? = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (replacement : replaceValueAt index child arguments = some replaced)
    (childDeep : child.HasDeepType signatures plan world fieldType)
    (childCode : child.HasPlanCode plan)
    (frame : ∀ replacementValue replacementArguments,
      replaceValueAt index replacementValue arguments = some
        replacementArguments →
      replacementValue.HasDeepType signatures plan world fieldType →
      replacementValue.HasPlanCode plan →
      (Value.constructed instantiation replacementArguments).HasDeepType
        signatures plan world instantiation.resultType ∧
      (Value.constructed instantiation replacementArguments).HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.constructed instantiation arguments))
      (.member name index :: rest) = .ok updated) :
    updated.HasDeepType signatures plan world instantiation.resultType ∧
      updated.HasPlanCode plan := by
  rw [updateResolvedValue_member_eq plan expected modify instantiation
    arguments replaced name index selected child rest found recursive replacement]
    at done
  cases done
  exact frame child replaced replacement childDeep childCode

/-- Replacing one payload preserves a pointwise type relation on every
type/value pair in the constructor's zipped payload vector. -/
private theorem replaceValueAt_preserves_zip
    (relation : Ty → Value → Prop) :
    ∀ (index : Nat) (types : List Ty) (arguments replaced : List Value)
      (fieldType : Ty) (replacement : Value),
      types.length = arguments.length →
      (∀ pair, pair ∈ List.zip types arguments → relation pair.1 pair.2) →
      types[index]? = some fieldType →
      relation fieldType replacement →
      replaceValueAt index replacement arguments = some replaced →
      types.length = replaced.length ∧
        ∀ pair, pair ∈ List.zip types replaced → relation pair.1 pair.2 := by
  intro index
  induction index with
  | zero =>
      intro types arguments replaced fieldType replacement lengths old slot
        replacementTyped written
      cases types with
      | nil => simp at slot
      | cons first restTypes =>
          cases arguments with
          | nil => simp [replaceValueAt] at written
          | cons firstValue restValues =>
              simp only [List.getElem?_cons_zero] at slot
              cases slot
              simp [replaceValueAt] at written
              cases written
              have tailLengths : restTypes.length = restValues.length := by
                simpa using lengths
              constructor
              · simpa using tailLengths
              · intro pair member
                simp only [List.zip, List.zipWith, List.mem_cons] at member
                rcases member with head | tail
                · cases head
                  exact replacementTyped
                · exact old pair (by simp [List.zip, List.zipWith, tail])
  | succ index inductionHypothesis =>
      intro types arguments replaced fieldType replacement lengths old slot
        replacementTyped written
      cases types with
      | nil => simp at slot
      | cons first restTypes =>
          cases arguments with
          | nil => simp [replaceValueAt] at written
          | cons firstValue restValues =>
              simp only [List.getElem?_cons_succ] at slot
              have tailLengths : restTypes.length = restValues.length := by
                simpa using lengths
              have oldTail : ∀ pair,
                  pair ∈ List.zip restTypes restValues →
                    relation pair.1 pair.2 := by
                intro pair member
                exact old pair (by
                  simp only [List.zip, List.zipWith, List.mem_cons]
                  exact Or.inr member)
              cases tailWrite : replaceValueAt index replacement restValues with
              | none =>
                  simp [replaceValueAt, tailWrite] at written
              | some replacedTail =>
                  simp [replaceValueAt, tailWrite] at written
                  cases written
                  obtain ⟨newLengths, newTail⟩ :=
                    inductionHypothesis restTypes restValues replacedTail
                      fieldType replacement tailLengths oldTail slot
                      replacementTyped tailWrite
                  constructor
                  · simpa using newLengths
                  · intro pair member
                    simp only [List.zip, List.zipWith, List.mem_cons] at member
                    rcases member with head | tail
                    · cases head
                      exact old (first, firstValue) (by simp [List.zip, List.zipWith])
                    · exact newTail pair tail

private theorem valueTypes?_of_zip
    (plan : Plan) :
    ∀ (types : List Ty) (arguments : List Value),
      types.length = arguments.length →
      (∀ pair, pair ∈ List.zip types arguments →
        pair.2.type? plan = some pair.1) →
      valueTypes? plan arguments = some types := by
  intro types
  induction types with
  | nil =>
      intro arguments lengths typed
      cases arguments with
      | nil => rfl
      | cons _ _ => cases lengths
  | cons first restTypes inductionHypothesis =>
      intro arguments lengths typed
      cases arguments with
      | nil => cases lengths
      | cons firstValue restValues =>
          have headTyped : firstValue.type? plan = some first :=
            typed (first, firstValue) (by simp [List.zip, List.zipWith])
          have tailLengths : restTypes.length = restValues.length := by
            simpa using lengths
          have tailTyped : ∀ pair,
              pair ∈ List.zip restTypes restValues →
                pair.2.type? plan = some pair.1 := by
            intro pair member
            exact typed pair (by
              simp only [List.zip, List.zipWith, List.mem_cons]
              exact Or.inr member)
          have restTyped := inductionHypothesis restValues tailLengths tailTyped
          simp [valueTypes?, headTyped, restTyped]

/-- Replacing one constructor payload with a value of the declared slot type
preserves the authoritative constructor metadata and every payload's deep
structural typing. -/
theorem Value.constructed_replace_hasDeepType
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (index : Nat) (fieldType : Ty) (replacement : Value)
    (old : (Value.constructed instantiation arguments).HasDeepType
      signatures plan world instantiation.resultType)
    (slot : instantiation.payloadTypes[index]? = some fieldType)
    (replacementDeep : replacement.HasDeepType signatures plan world fieldType)
    (written : replaceValueAt index replacement arguments = some replaced) :
    (Value.constructed instantiation replaced).HasDeepType signatures plan
      world instantiation.resultType := by
  have oldLength : instantiation.payloadTypes.length = arguments.length :=
    (old 1).2.2.2.1
  have oldShallow : ∀ pair,
      pair ∈ List.zip instantiation.payloadTypes arguments →
        pair.2.type? plan = some pair.1 := by
    intro pair member
    exact ((old 2).2.2.2.2 pair member).shallow
  obtain ⟨newLength, newShallow⟩ :=
    replaceValueAt_preserves_zip
      (fun type value => value.type? plan = some type) index
      instantiation.payloadTypes arguments replaced fieldType replacement
      oldLength oldShallow slot (replacementDeep 1).shallow written
  have newTypes : valueTypes? plan replaced =
      some instantiation.payloadTypes :=
    valueTypes?_of_zip plan instantiation.payloadTypes replaced newLength
      newShallow
  have outer : (Value.constructed instantiation replaced).type? plan =
      some instantiation.resultType := by
    simp [Value.type?, newTypes]
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      have oldPayloads : ∀ pair,
          pair ∈ List.zip instantiation.payloadTypes arguments →
            pair.2.HasDeepTypeFuel fuel signatures plan world pair.1 :=
        (old (fuel + 1)).2.2.2.2
      obtain ⟨payloadLength, payloads⟩ :=
        replaceValueAt_preserves_zip
          (fun type value =>
            value.HasDeepTypeFuel fuel signatures plan world type)
          index instantiation.payloadTypes arguments replaced fieldType
          replacement oldLength oldPayloads slot (replacementDeep fuel) written
      exact ⟨outer, rfl, (old 1).2.2.1, payloadLength, payloads⟩

theorem Value.constructed_replace_hasPlanCode
    (plan : Plan) (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (index : Nat) (replacement : Value)
    (old : (Value.constructed instantiation arguments).HasPlanCode plan)
    (replacementCode : replacement.HasPlanCode plan)
    (written : replaceValueAt index replacement arguments = some replaced) :
    (Value.constructed instantiation replaced).HasPlanCode plan := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      intro selected member
      rcases replaceValueAt_member index replacement arguments replaced
          selected written member with fresh | retained
      · subst selected
        exact replacementCode fuel
      · exact old (fuel + 1) selected retained

/-- The member-projection update no longer needs an abstract frame premise:
the payload slot type and the old constructor's invariants suffice. -/
theorem updateResolvedValue_member_preserves_from_parts
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected fieldType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (name : String) (index : Nat)
    (selected child updated : Value) (rest : List RuntimeProjection)
    (found : arguments[index]? = some selected)
    (slot : instantiation.payloadTypes[index]? = some fieldType)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (replacement : replaceValueAt index child arguments = some replaced)
    (oldDeep : (Value.constructed instantiation arguments).HasDeepType
      signatures plan world instantiation.resultType)
    (oldCode : (Value.constructed instantiation arguments).HasPlanCode plan)
    (childDeep : child.HasDeepType signatures plan world fieldType)
    (childCode : child.HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.constructed instantiation arguments))
      (.member name index :: rest) = .ok updated) :
    updated.HasDeepType signatures plan world instantiation.resultType ∧
      updated.HasPlanCode plan := by
  apply updateResolvedValue_member_preserves signatures plan world expected
    fieldType modify instantiation arguments replaced name index selected child
    updated rest found recursive replacement childDeep childCode
  · intro replacementValue replacementArguments replacedAt deep code
    exact ⟨Value.constructed_replace_hasDeepType signatures plan world
        instantiation arguments replacementArguments index fieldType
        replacementValue oldDeep slot deep replacedAt,
      Value.constructed_replace_hasPlanCode plan instantiation arguments
        replacementArguments index replacementValue oldCode code replacedAt⟩
  · exact done

/-- A successful place write decomposes into a matching root cell, a
successful recursive structural update, and a concrete heap write. -/
theorem writeResolvedPlace_done_components
    (plan : Plan) (state finalState : RuntimeState)
    (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value)
    (updated : Value)
    (done : writeResolvedPlace plan state place modify =
      .done updated finalState) :
    ∃ cell,
      state.read? place.location = some cell ∧
      cell.type = place.rootType ∧
      updateResolvedValue plan place.valueType modify
        (initialRootValue cell) place.projections = .ok updated ∧
      updated.type? plan = some place.rootType ∧
      state.write? place.location (some updated) = some finalState := by
  unfold writeResolvedPlace at done
  cases found : state.read? place.location with
  | none => simp [found] at done
  | some cell =>
      simp only [found] at done
      by_cases sameType : cell.type = place.rootType
      · have noMismatch : (cell.type != place.rootType) = false := by
          simp [sameType]
        rw [noMismatch] at done
        simp only [Bool.false_eq_true, ↓reduceIte] at done
        cases updateResult : updateResolvedValue plan place.valueType modify
            (initialRootValue cell) place.projections with
        | error error =>
            rw [updateResult] at done
            cases done
        | ok next =>
            rw [updateResult] at done
            by_cases nextType : next.type? plan = some place.rootType
            · simp [nextType] at done
              cases written : state.write? place.location (some next) with
              | none => simp [written] at done
              | some nextState =>
                  simp [written] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact ⟨cell, rfl, sameType, updateResult, nextType,
                    written⟩
            · simp [nextType] at done
      · simp [sameType] at done

/-- The assignment's final structural write preserves both established
runtime invariants under the precise update contract above. -/
theorem writeResolvedPlace_done_preserves_deep_and_code
    (signatures : ProgramSignatures) (plan : Plan)
    (state finalState : RuntimeState) (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value)
    (updated : Value)
    (deepHeap : state.HasDeepTypes signatures plan)
    (codeHeap : state.HasPlanCodes plan)
    (updatePreserves : place.UpdatePreservesDeepAndCode signatures plan state
      modify)
    (done : writeResolvedPlace plan state place modify =
      .done updated finalState) :
    finalState.HasDeepTypes signatures plan ∧
      finalState.HasPlanCodes plan := by
  obtain ⟨cell, found, sameType, updatedByPath, updatedType, written⟩ :=
    writeResolvedPlace_done_components plan state finalState place modify
      updated done
  obtain ⟨updatedDeep, updatedCode⟩ :=
    updatePreserves cell updated finalState found sameType updatedByPath
      updatedType written
  constructor
  · apply deepHeap.write?_some found written
    simpa [sameType] using updatedDeep
  · exact codeHeap.write?_some found updatedCode written

/-- For a root assignment with no projections, the structural-update
contract reduces to the leaf modifier's successful-result contract. -/
theorem ResolvedPlace.updatePreservesDeepAndCode_root
    (signatures : ProgramSignatures) (plan : Plan)
    (state : RuntimeState) (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value)
    (root : place.projections = [])
    (modifyPreserves : ∀ cell candidate finalState,
      state.read? place.location = some cell →
      cell.type = place.rootType →
      modify (initialRootValue cell) = .ok candidate →
      candidate.type? plan = some place.valueType →
      candidate.type? plan = some place.rootType →
      state.write? place.location (some candidate) = some finalState →
      candidate.HasDeepType signatures plan finalState place.rootType ∧
        candidate.HasPlanCode plan) :
    place.UpdatePreservesDeepAndCode signatures plan state modify := by
  intro cell candidate finalState found sameType updatedByPath rootType written
  rw [root] at updatedByPath
  simp only [updateResolvedValue] at updatedByPath
  cases modified : modify (initialRootValue cell) with
  | error error =>
      rw [modified] at updatedByPath
      change Except.error error = Except.ok candidate at updatedByPath
      cases updatedByPath
  | ok modifiedValue =>
      by_cases valueType : modifiedValue.type? plan = some place.valueType
      · rw [modified] at updatedByPath
        change (if modifiedValue.type? plan = some place.valueType then
            Except.ok modifiedValue else
            Except.error (RuntimeError.typeMismatch place.valueType
              (modifiedValue.type? plan))) = .ok candidate at updatedByPath
        simp [valueType] at updatedByPath
        cases updatedByPath
        exact modifyPreserves cell candidate finalState found sameType
          modified valueType rootType written
      · rw [modified] at updatedByPath
        change (if modifiedValue.type? plan = some place.valueType then
            Except.ok modifiedValue else
            Except.error (RuntimeError.typeMismatch place.valueType
              (modifiedValue.type? plan))) = .ok candidate at updatedByPath
        simp [valueType] at updatedByPath

/-- Executing a root assignment preserves both invariants under a contract
on the leaf callback alone.  Projected assignments use the general theorem
and still need an inductive proof for `updateResolvedValue`. -/
theorem writeResolvedPlace_done_preserves_root_deep_and_code
    (signatures : ProgramSignatures) (plan : Plan)
    (state finalState : RuntimeState) (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value)
    (updated : Value)
    (deepHeap : state.HasDeepTypes signatures plan)
    (codeHeap : state.HasPlanCodes plan)
    (root : place.projections = [])
    (modifyPreserves : ∀ cell candidate nextState,
      state.read? place.location = some cell →
      cell.type = place.rootType →
      modify (initialRootValue cell) = .ok candidate →
      candidate.type? plan = some place.valueType →
      candidate.type? plan = some place.rootType →
      state.write? place.location (some candidate) = some nextState →
      candidate.HasDeepType signatures plan nextState place.rootType ∧
        candidate.HasPlanCode plan)
    (done : writeResolvedPlace plan state place modify =
      .done updated finalState) :
    finalState.HasDeepTypes signatures plan ∧
      finalState.HasPlanCodes plan := by
  apply writeResolvedPlace_done_preserves_deep_and_code signatures plan
    state finalState place modify updated deepHeap codeHeap
  · exact place.updatePreservesDeepAndCode_root signatures plan state modify
      root modifyPreserves
  · exact done

/-- The evaluator's parameter/pattern binding helper keeps static code
provenance in the heap when the supplied values have that provenance. -/
theorem bindValues_ok_preserves_plan_codes
    (plan : Plan) (bindings : List (TypedBinder × Value))
    (environment finalEnvironment : Environment)
    (state finalState : RuntimeState)
    (typing : state.HasPlanCodes plan)
    (inputs : ∀ binding, binding ∈ bindings → binding.2.HasPlanCode plan)
    (bound : bindValues plan environment state bindings =
      .ok (finalEnvironment, finalState)) :
    finalState.HasPlanCodes plan := by
  induction bindings generalizing environment state with
  | nil =>
      simp [bindValues] at bound
      obtain ⟨rfl, rfl⟩ := bound
      exact typing
  | cons binding rest inductionHypothesis =>
      obtain ⟨binder, value⟩ := binding
      have valueCode : value.HasPlanCode plan :=
        inputs (binder, value) (List.Mem.head rest)
      by_cases typed : value.type? plan = some binder.scheme.body
      · simp [bindValues, typed, bne] at bound
        have restInputs : ∀ pair, pair ∈ rest →
            pair.2.HasPlanCode plan := by
          intro pair member
          exact inputs pair (List.Mem.tail (binder, value) member)
        exact inductionHypothesis _ _
          (typing.allocate_some binder.scheme.body value valueCode)
          restInputs bound
      · simp [bindValues, typed, bne] at bound
        change Except.error _ = Except.ok (finalEnvironment, finalState) at bound
        cases bound

theorem unit_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) :
    Value.hasType signatures plan (fuel + 1) .unit .unit = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.unit, Nat.add_one]
  rw [Value.validateTypeFuel.eq_2]
  rfl

theorem bool_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (value : Bool) :
    Value.hasType signatures plan (fuel + 1) .bool (.bool value) = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.bool, Nat.add_one]
  rw [Value.validateTypeFuel.eq_3]
  rfl

theorem word_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (value : Core.Word) :
    Value.hasType signatures plan (fuel + 1) .word (.word value) = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.word, Nat.add_one]
  rw [Value.validateTypeFuel.eq_4]
  rfl

theorem proxy_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (inner : Ty) :
    Value.hasType signatures plan (fuel + 1) (.proxy inner) (.proxy inner) =
      true := by
  unfold Value.hasType Value.hasTypeFuel
  rw [Nat.add_one, Value.validateTypeFuel.eq_7]
  split
  · change true = true
    rfl
  · contradiction

theorem zero_fuel_validateType (signatures : ProgramSignatures) (plan : Plan)
    (expected : Ty) (value : Value) :
    value.validateTypeFuel 0 signatures plan expected = .outOfFuel := by
  rw [Value.validateTypeFuel.eq_1]

theorem zero_fuel_runTrusted (plan : Plan) (entry : Key)
    (arguments : List Value) (state : RuntimeState) :
    runTrusted plan entry arguments 0 state = .outOfFuel state := by
  rfl

theorem run_eq_runWithValidationFuel (signatures : ProgramSignatures)
    (plan : Plan) (entry : Key) (arguments : List Value) (fuel : Nat)
    (state : RuntimeState) :
    run signatures plan entry arguments fuel state =
      runWithValidationFuel signatures plan entry arguments fuel fuel state := by
  rfl

theorem run_done_has_inferredBodyType
    (signatures : ProgramSignatures) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (done : run signatures plan entry arguments fuel initial =
      .done value finalState) :
    value.type? plan = some specialized.function.inferredBodyType := by
  exact runWithValidationFuel_done_has_inferredBodyType signatures plan entry
    arguments fuel fuel initial finalState value specialized exact done

theorem run?_some_iff (signatures : ProgramSignatures) (plan : Plan)
    (entry : Key) (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value) :
    run? signatures plan entry arguments fuel initial =
        some (value, finalState) ↔
      run signatures plan entry arguments fuel initial =
        .done value finalState := by
  unfold run?
  split <;> simp_all

theorem run?_some_has_inferredBodyType
    (signatures : ProgramSignatures) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (success : run? signatures plan entry arguments fuel initial =
      some (value, finalState)) :
    value.type? plan = some specialized.function.inferredBodyType := by
  apply run_done_has_inferredBodyType signatures plan entry arguments fuel
    initial finalState value specialized exact
  exact (run?_some_iff signatures plan entry arguments fuel initial finalState
    value).mp success

end Solcore.Frontend.SourceTypedRuntime
