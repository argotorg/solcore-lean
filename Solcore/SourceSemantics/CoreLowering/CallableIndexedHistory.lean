import Solcore.Frontend.SourceCoreCallableIndexedDispatch
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation

/-! Indexed native carriers with separately carried ghost ancestry.
A table lookup alone grants no execution-history receipt. The relation below
requires an independent recursive metadata derivation, retained only in Prop.
Actual dispatch preserves that derivation through the validated cache edge.
These are protocol-local laws; whole-program production of related frames is
not inferred from native typing or from a successful carrier decoder. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedHistory
open Core Frontend CallableAncestryPairedLookup
abbrev NativeFrame := SourceCoreCallableIndexedFrames.Frame
abbrev GhostFrame := SourceCoreCallablePairedFrames.Frame
abbrev MetadataState := SourceCoreCallableAncestryReadRecipes.State

/-- Stable native state tokens retain their exact table location and a ghost
metadata derivation. The ghost is not reconstructed during runtime lookup. -/
inductive Carries {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) :
    NativeFrame → GhostFrame → Option MetadataState → Prop where
  | empty : Carries inputs table .empty .empty none
  | state {position : Nat} {ghost : GhostFrame} {metadata : MetadataState}
      (stored : table.stateAt? position = some metadata)
      (history : Authenticates inputs ghost (some metadata)) :
      Carries inputs table (.state (Int.ofNat position)) ghost (some metadata)

theorem Carries.authenticates {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (carried : Carries inputs table native ghost metadata) : Authenticates inputs ghost metadata := by
  cases carried with
  | empty => exact .empty
  | state _ history => exact history

theorem Carries.lookup {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (carried : Carries inputs table native ghost metadata) :
    SourceCoreCallableIndexedDispatch.lookup? table native = some metadata := by
  cases carried with
  | empty => rfl
  | state stored _ => simp [SourceCoreCallableIndexedDispatch.lookup?, SourceCoreCallableIndexedFrames.naturalIndex?, stored]

theorem Carries.state_shape {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : MetadataState}
    (carried : Carries inputs table native ghost (some metadata)) :
    ∃ position, native = .state (Int.ofNat position) ∧ table.stateAt? position = some metadata := by
  cases carried with
  | state stored _ => exact ⟨_, rfl, stored⟩

theorem Carries.not_invalid {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (carried : Carries inputs table native ghost metadata) : native ≠ .invalid := by cases carried <;> simp

/-- A transient view carries the actual preparation receipt at its caller.
Its lexical application target is intentionally not chosen at read time. -/
inductive Current {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) :
    NativeFrame → GhostFrame → Prop where
  | stable {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
      (carried : Carries inputs table native ghost metadata) : Current inputs table native ghost
  | reading {position : Nat} {caller : GhostFrame} {metadata : MetadataState} {id target : Word}
      (carried : Carries inputs table (.state (Int.ofNat position)) caller (some metadata))
      (read : SourceCoreCallableAncestryReadRecipes.Read inputs metadata id target)
      (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs metadata id target = .ok read) :
      Current inputs table (.view id target (Int.ofNat position)) (.view id target caller)

theorem read_history {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {native : NativeFrame} {caller : GhostFrame} {metadata : MetadataState} {id target : Word}
    (carried : Carries inputs table native caller (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs metadata id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs metadata id target = .ok read) :
    Current inputs table (SourceCoreCallableIndexedDispatch.readFrame id target native) (.view id target caller) := by
  cases carried with
  | state stored history => exact .reading (.state stored history) read prepared

/-- Reification is a theorem about the metadata domain, not a decoder of
runtime history: its input already contains the ghost authentication. -/
theorem reify {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Authenticates graph.inputs ghost metadata) :
    ∃ native, Carries graph.inputs graph.table native ghost metadata := by
  have indexed := lookupIndex_complete
    (CallableAncestryPairedValidation.valid_closed graph.inputs graph.validated) history
  cases metadata with
  | none => cases history; exact ⟨.empty, .empty⟩
  | some metadata =>
    obtain ⟨position, _, stored⟩ := indexed
    exact ⟨.state (Int.ofNat position), .state stored history⟩

private theorem checkedState_eq {table : Table} {position : Nat} {metadata : MetadataState}
    (stored : table.stateAt? position = some metadata) :
    SourceCoreCallableIndexedDispatch.checkedState table position = .state (Int.ofNat position) := by
  simp [SourceCoreCallableIndexedDispatch.checkedState, stored]

theorem named_history {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base) {origin : Word} {position : Nat}
    (selected : graph.table.namedAt? origin = some position) :
    ∃ metadata, Carries graph.inputs graph.table
      (SourceCoreCallableIndexedDispatch.namedFrame graph.table origin) (.named origin) (some metadata) := by
  obtain ⟨metadata, generated, stored⟩ :=
    (CallableAncestryPairedValidation.valid_sound graph.inputs graph.validated).named selected
  refine ⟨metadata, ?_⟩
  simp only [SourceCoreCallableIndexedDispatch.namedFrame, selected, checkedState_eq stored]
  exact .state stored (.named generated)

theorem named_complete {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base) {origin : Word} {metadata : MetadataState}
    (generated : SourceCoreCallableAncestryPairedPreparation.named? graph.inputs origin = some metadata) :
    Carries graph.inputs graph.table (SourceCoreCallableIndexedDispatch.namedFrame graph.table origin)
      (.named origin) (some metadata) := by
  obtain ⟨position, selected, stored⟩ :=
    (CallableAncestryPairedValidation.valid_closed graph.inputs graph.validated).named generated
  simp only [SourceCoreCallableIndexedDispatch.namedFrame, selected, checkedState_eq stored]
  exact .state stored (.named generated)

private theorem plainRows_eq (table : Table) (origin : Word) (position : Nat)
    (rows : List SourceCoreCallableAncestryPairedCache.LambdaEdge) :
    SourceCoreCallableIndexedDispatch.plainRows table origin (Int.ofNat position) rows =
      if rows.any (fun edge => decide (edge.state = position ∧ edge.origin = origin)) then
        SourceCoreCallableIndexedDispatch.checkedState table position else .invalid := by
  induction rows with
  | nil => rfl
  | cons edge rest ih =>
    by_cases sameOrigin : edge.origin = origin
    · by_cases samePosition : edge.state = position
      · simp only [SourceCoreCallableIndexedDispatch.plainRows, sameOrigin, samePosition, and_self, ↓reduceIte, List.any_cons, decide_true, Bool.true_or]
      · simp only [SourceCoreCallableIndexedDispatch.plainRows, sameOrigin, true_and, Int.ofNat.injEq, Ne.symm samePosition, ↓reduceIte, List.any_cons, samePosition, false_and, decide_false, Bool.false_or]
        exact ih
    · simp only [SourceCoreCallableIndexedDispatch.plainRows, sameOrigin, false_and, ↓reduceIte, List.any_cons, and_false, decide_false, Bool.false_or]
      exact ih

private theorem viewRows_eq (table : Table) (origin id : Word) (caller lexical : Nat)
    (rows : List SourceCoreCallableAncestryPairedCache.ViewEdge) :
    SourceCoreCallableIndexedDispatch.viewRows table origin id (Int.ofNat caller) (Int.ofNat lexical) rows =
      match rows.find? (fun edge => decide
        (edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = id ∧ edge.target = origin)) with
      | none => .invalid
      | some edge => SourceCoreCallableIndexedDispatch.checkedState table edge.destination := by
  induction rows with
  | nil => rfl
  | cons edge rest ih =>
    by_cases same : edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = id ∧ edge.target = origin
    · simp only [SourceCoreCallableIndexedDispatch.viewRows, same.1, same.2.1, same.2.2.1, same.2.2.2, and_self, ↓reduceIte, List.find?_cons, decide_true]
    · have reordered : ¬(edge.target = origin ∧ edge.view = id ∧ caller = edge.caller ∧ lexical = edge.lexical) := by
        intro h; exact same ⟨h.2.2.1.symm, h.2.2.2.symm, h.2.1, h.1⟩
      simp only [SourceCoreCallableIndexedDispatch.viewRows, Int.ofNat.injEq, reordered, ↓reduceIte, List.find?_cons, same, decide_false]
      exact ih

private theorem viewRows_table (table : Table) (origin id : Word) (caller lexical : Nat) :
    SourceCoreCallableIndexedDispatch.viewRows table origin id (Int.ofNat caller) (Int.ofNat lexical) table.views =
      match table.viewAt? caller lexical id origin with
      | none => .invalid
      | some position => SourceCoreCallableIndexedDispatch.checkedState table position := by
  rw [viewRows_eq]
  unfold SourceCoreCallableAncestryPairedCache.Table.viewAt?
  cases table.views.find? _ <;> rfl

/-- An ordinary edge preserves metadata but extends the ghost derivation. -/
theorem ordinary_history {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {position : Nat} {ghost : GhostFrame} {metadata : MetadataState} {origin : Word}
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) ghost (some metadata))
    (allowed : graph.table.lambdaAllowed position origin = true) :
    Carries graph.inputs graph.table
      (SourceCoreCallableIndexedDispatch.plainRows graph.table origin (Int.ofNat position) graph.table.lambdas)
      (.lambda origin ghost) (some metadata) := by
  cases carried with
  | state stored history =>
    rw [plainRows_eq]
    change Carries _ _ (if graph.table.lambdaAllowed position origin then _ else _) _ _
    rw [allowed, if_pos rfl, checkedState_eq stored]
    exact .state stored (.lambda history
      ((CallableAncestryPairedValidation.valid_sound graph.inputs graph.validated).lambda stored allowed))

/-- Caller and lexical histories remain distinct when an indexed view edge
is applied. Soundness comes from the real validated preparation table. -/
theorem applied_history {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {callerIndex lexicalIndex destination : Nat} {callerGhost lexicalGhost : GhostFrame}
    {caller lexical : MetadataState} {id target : Word}
    (callerCarried : Carries graph.inputs graph.table (.state (Int.ofNat callerIndex)) callerGhost (some caller))
    (lexicalCarried : Carries graph.inputs graph.table (.state (Int.ofNat lexicalIndex)) lexicalGhost (some lexical))
    (selected : graph.table.viewAt? callerIndex lexicalIndex id target = some destination) :
    ∃ metadata, Carries graph.inputs graph.table
      (SourceCoreCallableIndexedDispatch.viewRows graph.table target id (Int.ofNat callerIndex)
        (Int.ofNat lexicalIndex) graph.table.views)
      (.appliedView id target callerGhost lexicalGhost) (some metadata) ∧
      SourceCoreCallableAncestryPairedPreparation.view? graph.inputs caller lexical id target = some metadata := by
  cases callerCarried with
  | state callerStored callerHistory =>
    cases lexicalCarried with
    | state lexicalStored lexicalHistory =>
      obtain ⟨metadata, generated, stored⟩ :=
        (CallableAncestryPairedValidation.valid_sound graph.inputs graph.validated).view callerStored lexicalStored selected
      refine ⟨metadata, ?_, generated⟩
      simp only [viewRows_table, selected, checkedState_eq stored]
      exact .state stored (.appliedView callerHistory lexicalHistory generated)

private theorem ordinary_of_valid {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {position : Nat} {ghost : GhostFrame} {metadata : MetadataState} {origin : Word}
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) ghost (some metadata))
    (valid : SourceCoreCallableIndexedDispatch.plainRows graph.table origin (Int.ofNat position)
      graph.table.lambdas ≠ .invalid) :
    Carries graph.inputs graph.table
      (SourceCoreCallableIndexedDispatch.plainRows graph.table origin (Int.ofNat position) graph.table.lambdas)
      (.lambda origin ghost) (some metadata) := by
  have allowed : graph.table.lambdaAllowed position origin = true := by
    rw [plainRows_eq] at valid
    change (if graph.table.lambdaAllowed position origin then _ else _) ≠ _ at valid
    cases h : graph.table.lambdaAllowed position origin
    · simp [h] at valid
    · rfl
  exact ordinary_history graph carried allowed

private theorem applied_of_valid {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {callerIndex lexicalIndex : Nat} {callerGhost lexicalGhost : GhostFrame}
    {caller lexical : MetadataState} {id target : Word}
    (callerCarried : Carries graph.inputs graph.table (.state (Int.ofNat callerIndex)) callerGhost (some caller))
    (lexicalCarried : Carries graph.inputs graph.table (.state (Int.ofNat lexicalIndex)) lexicalGhost (some lexical))
    (valid : SourceCoreCallableIndexedDispatch.viewRows graph.table target id (Int.ofNat callerIndex)
      (Int.ofNat lexicalIndex) graph.table.views ≠ .invalid) :
    ∃ metadata, Carries graph.inputs graph.table
      (SourceCoreCallableIndexedDispatch.viewRows graph.table target id (Int.ofNat callerIndex)
        (Int.ofNat lexicalIndex) graph.table.views)
      (.appliedView id target callerGhost lexicalGhost) (some metadata) := by
  rw [viewRows_table] at valid
  cases selected : graph.table.viewAt? callerIndex lexicalIndex id target with
  | none => simp [selected] at valid
  | some destination =>
    obtain ⟨metadata, carried, _⟩ := applied_history graph callerCarried lexicalCarried selected
    exact ⟨metadata, carried⟩

private theorem stable_selection {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {ghost : GhostFrame} {metadata : Option MetadataState} (history : Authenticates inputs ghost metadata)
    (origin : Word) (lexical : GhostFrame) :
    SourceCoreCallablePairedFrames.selectedFrame origin lexical ghost = .lambda origin lexical := by
  cases history <;> rfl

/-- Successful actual finite dispatch constructs the ghost successor from its
carried parents. This does not turn arbitrary valid indices into histories. -/
theorem selection_history {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {lexicalNative currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {lexical : MetadataState} {origin : Word}
    (lexicalCarried : Carries graph.inputs graph.table lexicalNative lexicalGhost (some lexical))
    (current : Current graph.inputs graph.table currentNative currentGhost)
    (valid : SourceCoreCallableIndexedDispatch.selectedFrame graph.table origin lexicalNative currentNative ≠ .invalid) :
    ∃ metadata, Carries graph.inputs graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame graph.table origin lexicalNative currentNative)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some metadata) := by
  cases lexicalCarried with
  | state lexicalStored lexicalHistory =>
    cases current with
    | stable carried =>
      rw [stable_selection carried.authenticates]
      cases carried with
      | empty => exact ⟨lexical, ordinary_of_valid graph (.state lexicalStored lexicalHistory) valid⟩
      | state stored history => exact ⟨lexical, ordinary_of_valid graph (.state lexicalStored lexicalHistory) valid⟩
    | reading callerCarried read prepared =>
      next callerIndex callerGhost caller id target =>
        by_cases sameTarget : target = origin
        · subst target
          simp only [SourceCoreCallableIndexedDispatch.selectedFrame, SourceCoreCallablePairedFrames.selectedFrame,
            ↓reduceIte] at valid ⊢
          exact applied_of_valid graph callerCarried (.state lexicalStored lexicalHistory) valid
        · simp only [SourceCoreCallableIndexedDispatch.selectedFrame, SourceCoreCallablePairedFrames.selectedFrame,
            sameTarget, ↓reduceIte] at valid ⊢
          exact ⟨lexical, ordinary_of_valid graph (.state lexicalStored lexicalHistory) valid⟩

/-- Actual independent read/application preparation is sufficient for indexed
selection. The cached destination is found by closure of the completed table. -/
theorem applied_complete {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {callerIndex lexicalIndex : Nat} {callerGhost lexicalGhost : GhostFrame}
    {caller lexical : MetadataState} {id target : Word}
    (callerCarried : Carries graph.inputs graph.table (.state (Int.ofNat callerIndex)) callerGhost (some caller))
    (lexicalCarried : Carries graph.inputs graph.table (.state (Int.ofNat lexicalIndex)) lexicalGhost (some lexical))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs caller id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs caller id target = .ok read)
    (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)
    (appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexical = .ok applied) :
    Carries graph.inputs graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame graph.table target (.state (Int.ofNat lexicalIndex))
        (.view id target (Int.ofNat callerIndex)))
      (.appliedView id target callerGhost lexicalGhost) (some (read.after lexical)) := by
  have generated : SourceCoreCallableAncestryPairedPreparation.view? graph.inputs caller lexical id target =
      some (read.after lexical) := by
    simp [SourceCoreCallableAncestryPairedPreparation.view?, prepared, appliedPrepared, Except.toOption]
  obtain ⟨_, callerShape, callerStored⟩ := callerCarried.state_shape
  obtain ⟨_, lexicalShape, lexicalStored⟩ := lexicalCarried.state_shape
  cases callerShape
  cases lexicalShape
  obtain ⟨destination, selected, _⟩ :=
    (CallableAncestryPairedValidation.valid_closed graph.inputs graph.validated).view callerStored lexicalStored generated
  obtain ⟨metadata, carried, actual⟩ := applied_history graph callerCarried lexicalCarried selected
  have same : metadata = read.after lexical := Option.some.inj (actual.symm.trans generated)
  subst metadata
  simpa only [SourceCoreCallableIndexedDispatch.selectedFrame, ↓reduceIte] using carried

/-- Ordinary lambda entry is total for its actual allowed metadata rule,
including entry from a stable state of a different caller. -/
theorem ordinary_complete {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {lexicalNative currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {lexical : MetadataState} {current : Option MetadataState} {origin : Word}
    (lexicalCarried : Carries graph.inputs graph.table lexicalNative lexicalGhost (some lexical))
    (currentCarried : Carries graph.inputs graph.table currentNative currentGhost current)
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed graph.inputs lexical origin = true) :
    Carries graph.inputs graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame graph.table origin lexicalNative currentNative)
      (.lambda origin lexicalGhost) (some lexical) := by
  cases lexicalCarried with
  | state stored history =>
    have cached := (CallableAncestryPairedValidation.valid_closed graph.inputs graph.validated).lambda stored allowed
    cases currentCarried <;> exact ordinary_history graph (.state stored history) cached

/-- The administrative cell stores only the bounded-depth native carrier;
its ghost derivation remains separate from the Core store. -/
structure CellState {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (layout : SourceCoreCallableIndexedFrames.Layout) (location : Location)
    (native : NativeFrame) (ghost : GhostFrame) (store : Store) : Prop where
  read : store.read? location = some (SourceCoreCallableIndexedFrames.encode layout native)
  history : Current inputs table native ghost

end Solcore.SourceSemantics.CoreLowering.CallableIndexedHistory
