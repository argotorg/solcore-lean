import Solcore.Frontend.SourceCoreCallableIndexedDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AncestryPaired
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AppliedViews
import Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps
import Solcore.Core.Derived
import Solcore.Frontend.SourceCoreAllocationLayouts
import Solcore.SourceSemantics.CoreLowering.Internal.Data.HeapsAndBindings
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GenericHeaps
import Solcore.Frontend.SourceCoreCallableIndexedAncestry
import Solcore.Frontend.SourceCoreCallableIndexedPrograms
import Solcore.Frontend.SourceCoreUnifiedRuntime
import Solcore.SourceSemantics.Dynamic.ProgramOutcome

/-!
# Indexed callables: allocation and frames

The history, protocol, frames and allocation of indexed callable carriers, snapshots and renaming, with the receiver tables and observations of public faults.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedHistory
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedContextFrames
/-! Finite ordinary Core evaluation of table-derived indexed dispatch. These
laws concern exact native values and unchanged stores. Source history, graph
coverage and actual closure provenance are separate owned proof boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedContextFrames
open Core Frontend.SourceCoreCallableIndexedFrames Frontend.SourceCoreCallableIndexedDispatch
open DataEquality (Selects)
abbrev IndexedFrame := Frontend.SourceCoreCallableIndexedFrames.Frame

theorem literal_evaluates (layout : Layout) (frame : IndexedFrame)
    (environment : Environment) (store : Store) :
    Evaluates environment store (literal layout frame) (encode layout frame) store := by
  cases frame with
  | empty => exact .construct .unit
  | state index => exact .construct .integer
  | view id target caller => exact .construct (.pair .word (.pair .word .integer))
  | invalid => exact .construct .unit

private theorem integerEq_evaluates {environment : Environment} {expression : Expr} {value : Int}
    (selected : Selects environment expression (.integer value)) (expected : Int) (store : Store) :
    Evaluates environment store (.binary .integerEq expression (.integer expected)) (.bool (value == expected)) store :=
  .binary (selected.evaluates store) .integer rfl

private theorem wordEq_evaluates {environment : Environment} {expression : Expr} {value : Word}
    (selected : Selects environment expression (.word value)) (expected : Word) (store : Store) :
    Evaluates environment store (.binary .wordEq expression (.word expected)) (.bool (value == expected)) store :=
  .binary (selected.evaluates store) .word rfl

theorem plainDispatch_evaluates {layout : Layout} {environment : Environment} {lexical : Expr} {index : Int}
    (table : Table) (origin : Word) (selected : Selects environment lexical (.integer index))
    (rows : List LambdaEdge) (store : Store) :
    Evaluates environment store (plainDispatch table layout origin lexical rows)
      (encode layout (plainRows table origin index rows)) store := by
  induction rows with
  | nil => exact .construct .unit
  | cons edge rest ih =>
    by_cases owned : edge.origin = origin
    · simp only [plainDispatch, if_pos owned]
      by_cases same : index = Int.ofNat edge.state
      · simp only [plainRows, owned, same, and_self, ↓reduceIte]
        exact .ifTrue (by simpa [same] using integerEq_evaluates selected (Int.ofNat edge.state) store)
          (literal_evaluates layout _ environment store)
      · simp only [plainRows, owned, same, and_false, ↓reduceIte]
        exact .ifFalse (by simpa only [beq_eq_false_iff_ne.mpr same] using integerEq_evaluates selected (Int.ofNat edge.state) store) ih
    · simpa only [plainDispatch, plainRows, owned, false_and, ↓reduceIte] using ih

theorem viewDispatch_evaluates {layout : Layout} {environment : Environment}
    {id caller lexical : Expr} {view : Word} {callerIndex lexicalIndex : Int}
    (table : Table) (origin : Word)
    (idSelected : Selects environment id (.word view))
    (callerSelected : Selects environment caller (.integer callerIndex))
    (lexicalSelected : Selects environment lexical (.integer lexicalIndex))
    (rows : List ViewEdge) (store : Store) :
    Evaluates environment store (viewDispatch table layout origin id caller lexical rows)
      (encode layout (viewRows table origin view callerIndex lexicalIndex rows)) store := by
  induction rows with
  | nil => exact .construct .unit
  | cons edge rest ih =>
    by_cases owned : edge.target = origin
    · simp only [viewDispatch, if_pos owned]
      by_cases viewSame : edge.view = view
      · by_cases callerSame : callerIndex = Int.ofNat edge.caller
        · by_cases lexicalSame : lexicalIndex = Int.ofNat edge.lexical
          · simp only [viewRows, owned, viewSame, callerSame, lexicalSame, and_self, ↓reduceIte]
            exact .ifTrue (.ifTrue (by simpa [viewSame] using wordEq_evaluates idSelected edge.view store)
                (.ifTrue (by simpa [callerSame] using integerEq_evaluates callerSelected (Int.ofNat edge.caller) store)
                  (by simpa [lexicalSame] using integerEq_evaluates lexicalSelected (Int.ofNat edge.lexical) store)))
              (literal_evaluates layout _ environment store)
          · simp only [viewRows, owned, viewSame, callerSame, lexicalSame, and_false, ↓reduceIte]
            exact .ifFalse (.ifTrue (by simpa [viewSame] using wordEq_evaluates idSelected edge.view store)
                (.ifTrue (by simpa [callerSame] using integerEq_evaluates callerSelected (Int.ofNat edge.caller) store)
                  (by simpa only [beq_eq_false_iff_ne.mpr lexicalSame] using integerEq_evaluates lexicalSelected (Int.ofNat edge.lexical) store)))
              (by simpa only [callerSame] using ih)
        · simp only [viewRows, owned, viewSame, callerSame, false_and, and_false, ↓reduceIte]
          exact .ifFalse (.ifTrue (by simpa [viewSame] using wordEq_evaluates idSelected edge.view store)
              (.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr callerSame] using integerEq_evaluates callerSelected (Int.ofNat edge.caller) store) .bool)) ih
      · simp only [viewRows, owned, viewSame, false_and, and_false, ↓reduceIte]
        exact .ifFalse (.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr (Ne.symm viewSame)] using wordEq_evaluates idSelected edge.view store) .bool) ih
    · simpa only [viewDispatch, viewRows, owned, false_and, ↓reduceIte] using ih

theorem lambdaFrame_evaluates {layout : Layout} {environment : Environment} {lexical current : Expr}
    {lexicalFrame currentFrame : IndexedFrame} (table : Table) (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) (store : Store) :
    Evaluates environment store (lambdaFrame table layout origin lexical current)
      (encode layout (selectedFrame table origin lexicalFrame currentFrame)) store := by
  cases lexicalFrame with
  | empty => exact .matchData (lexicalSelected.evaluates store) rfl rfl (.construct .unit)
  | invalid => exact .matchData (lexicalSelected.evaluates store) rfl rfl (.construct .unit)
  | view id target caller => exact .matchData (lexicalSelected.evaluates store) rfl rfl (.construct .unit)
  | state index =>
    apply Evaluates.matchData (lexicalSelected.evaluates store) rfl rfl
    cases currentFrame with
    | empty =>
      exact .matchData ((currentSelected.weaken (.integer index)).evaluates store) rfl rfl
        (plainDispatch_evaluates table origin (.var rfl) _ store)
    | state currentIndex =>
      exact .matchData ((currentSelected.weaken (.integer index)).evaluates store) rfl rfl
        (plainDispatch_evaluates table origin (.var rfl) _ store)
    | invalid =>
      exact .matchData ((currentSelected.weaken (.integer index)).evaluates store) rfl rfl
        (plainDispatch_evaluates table origin (.var rfl) _ store)
    | view id target caller =>
      apply Evaluates.matchData ((currentSelected.weaken (.integer index)).evaluates store) rfl rfl
      have targetSelected : Selects (.pair (.word id) (.pair (.word target) (.integer caller)) :: .integer index :: environment)
          (.first (.second (.var 0))) (.word target) := .first (.second (.var rfl))
      by_cases same : target = origin
      · simp only [selectedFrame, if_pos same]
        exact .ifTrue (by simpa [same] using wordEq_evaluates targetSelected origin store)
          (viewDispatch_evaluates table origin (.first (.var rfl))
            (.second (.second (.var rfl))) (.var rfl) _ store)
      · simp only [selectedFrame, if_neg same]
        exact .ifFalse (by simpa only [beq_eq_false_iff_ne.mpr same] using wordEq_evaluates targetSelected origin store)
          (plainDispatch_evaluates table origin (.var rfl) _ store)

theorem readView_evaluates {layout : Layout} {environment : Environment} {current : Expr}
    {currentFrame : IndexedFrame} (id target : Word)
    (selected : Selects environment current (encode layout currentFrame)) (store : Store) :
    Evaluates environment store (readView layout id target current)
      (encode layout (readFrame id target currentFrame)) store := by
  cases currentFrame with
  | empty => exact .matchData (selected.evaluates store) rfl rfl (.construct .unit)
  | state index => exact .matchData (selected.evaluates store) rfl rfl (.construct (.pair .word (.pair .word (.var rfl))))
  | view id target caller => exact .matchData (selected.evaluates store) rfl rfl (.construct .unit)
  | invalid => exact .matchData (selected.evaluates store) rfl rfl (.construct .unit)

theorem lambdaFrame_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : IndexedFrame} {table : Table} {origin : Word} {result : Value}
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame))
    (evaluated : Evaluates environment before (lambdaFrame table layout origin lexical current) result after) :
    result = encode layout (selectedFrame table origin lexicalFrame currentFrame) ∧ after = before :=
  evaluation_deterministic evaluated (lambdaFrame_evaluates table origin lexicalSelected currentSelected before)

theorem lambdaFrame_run {layout : Layout} {environment : Environment} {store : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : IndexedFrame} (table : Table) (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (lambdaFrame table layout origin lexical current) environment store) =
        .done (encode layout (selectedFrame table origin lexicalFrame currentFrame)) store) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (lambdaFrame table layout origin lexical current) environment store) = .done actual after →
        actual = encode layout (selectedFrame table origin lexicalFrame currentFrame) ∧ after = store) :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel (lambdaFrame_evaluates table origin lexicalSelected currentSelected store),
    fun _ _ _ ran => lambdaFrame_reflects lexicalSelected currentSelected (runStateful_evaluation_sound ran)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedContextFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol
/-! Actual indexed dispatch evaluation carries ghost metadata derivations.
The mutable current-frame reference is read through its exact native slot.
We use the real extra match binder and do not weaken arbitrary closure values
or stores by an alleged exact-equality theorem. These finite helper laws do not
claim that every closure or allocation produced by the compiler already carries
this invariant; that requires the surrounding emitted-protocol induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol
open Core Frontend CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch
open DataEquality (Selects)

/-- The lexical state match adds one integer slot before it executes current.
The premise is the actual child evaluation in that environment. -/
theorem lambdaFrame_read {layout : Layout} {environment : Environment} {store : Store}
    {lexical current : Expr} {position : Nat} {currentNative : NativeFrame}
    (table : SourceCoreCallableIndexedDispatch.Table) (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (currentRead : Evaluates (.integer (Int.ofNat position) :: environment) store
      (current.weakenAt 0) (encode layout currentNative) store) :
    Evaluates environment store (lambdaFrame table layout origin lexical current)
      (encode layout (selectedFrame table origin (.state (Int.ofNat position)) currentNative)) store := by
  apply Evaluates.matchData (lexicalSelected.evaluates store) rfl rfl
  cases currentNative with
  | empty =>
    exact .matchData currentRead rfl rfl
      (CallableIndexedContextFrames.plainDispatch_evaluates table origin (.var rfl) _ store)
  | state index =>
    exact .matchData currentRead rfl rfl
      (CallableIndexedContextFrames.plainDispatch_evaluates table origin (.var rfl) _ store)
  | invalid =>
    exact .matchData currentRead rfl rfl
      (CallableIndexedContextFrames.plainDispatch_evaluates table origin (.var rfl) _ store)
  | view id target caller =>
    apply Evaluates.matchData currentRead rfl rfl
    by_cases same : target = origin
    · simp only [selectedFrame, if_pos same]
      apply Evaluates.ifTrue (.binary (.first (.second (.var rfl))) .word ?_)
      · exact CallableIndexedContextFrames.viewDispatch_evaluates table origin
          (.first (.var rfl)) (.second (.second (.var rfl))) (.var rfl) _ store
      · simp [BinaryOp.apply, same]
    · simp only [selectedFrame, if_neg same]
      apply Evaluates.ifFalse (.binary (.first (.second (.var rfl))) .word ?_)
      · exact CallableIndexedContextFrames.plainDispatch_evaluates table origin (.var rfl) _ store
      · simp [BinaryOp.apply, same]

/-- Reading the actual administrative reference supplies the child premise.
No statement about arbitrary effectful reference expressions is used. -/
theorem lambdaFrame_load {layout : Layout} {environment : Environment} {store : Store}
    {lexical : Expr} {position referenceIndex location : Nat} {currentNative : NativeFrame}
    (table : SourceCoreCallableIndexedDispatch.Table) (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (read : store.read? location = some (encode layout currentNative)) :
    Evaluates environment store (lambdaFrame table layout origin lexical (.loadCell (.var referenceIndex)))
      (encode layout (selectedFrame table origin (.state (Int.ofNat position)) currentNative)) store := by
  apply lambdaFrame_read table origin lexicalSelected
  simpa only [Expr.weakenAt, Nat.zero_le, decide_true, ↓reduceIte] using
    (show Evaluates (.integer (Int.ofNat position) :: environment) store (.loadCell (.var (referenceIndex + 1)))
      (encode layout currentNative) store from .loadCell (.var reference) read)

/-- The real read-view helper turns a carried stable caller into its transient
read token; the factory receipt keeps the caller's occurrence-specific IDs. -/
theorem read_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {store : Store} {current : Expr}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : MetadataState} {id target : Word}
    (selected : Selects environment current (encode layout native))
    (carried : Carries graph.inputs graph.table native ghost (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs metadata id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs metadata id target = .ok read) :
    Evaluates environment store (readView layout id target current)
      (encode layout (readFrame id target native)) store ∧
    Current graph.inputs graph.table (readFrame id target native) (.view id target ghost) :=
  ⟨CallableIndexedContextFrames.readView_evaluates id target selected store,
    read_history carried read prepared⟩

theorem dispatch_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {store : Store} {lexical current : Expr}
    {lexicalNative currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word}
    (lexicalSelected : Selects environment lexical (encode layout lexicalNative))
    (currentSelected : Selects environment current (encode layout currentNative))
    (carried : Carries graph.inputs graph.table lexicalNative lexicalGhost (some metadata))
    (currentHistory : Current graph.inputs graph.table currentNative currentGhost)
    (valid : selectedFrame graph.table origin lexicalNative currentNative ≠ .invalid) :
    ∃ resultState,
      Evaluates environment store (lambdaFrame graph.table layout origin lexical current)
        (encode layout (selectedFrame graph.table origin lexicalNative currentNative)) store ∧
      Carries graph.inputs graph.table (selectedFrame graph.table origin lexicalNative currentNative)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  obtain ⟨resultState, history⟩ := selection_history graph carried currentHistory valid
  exact ⟨resultState, CallableIndexedContextFrames.lambdaFrame_evaluates graph.table origin lexicalSelected currentSelected store, history⟩

/-- A completed native dispatch is reflected against the same independently
carried parents. Native determinism supplies result/store equality only. -/
theorem dispatch_reflects {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {before after : Store} {lexical current : Expr}
    {lexicalNative currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word} {result : Value}
    (lexicalSelected : Selects environment lexical (encode layout lexicalNative))
    (currentSelected : Selects environment current (encode layout currentNative))
    (carried : Carries graph.inputs graph.table lexicalNative lexicalGhost (some metadata))
    (currentHistory : Current graph.inputs graph.table currentNative currentGhost)
    (valid : selectedFrame graph.table origin lexicalNative currentNative ≠ .invalid)
    (evaluated : Evaluates environment before (lambdaFrame graph.table layout origin lexical current) result after) :
    result = encode layout (selectedFrame graph.table origin lexicalNative currentNative) ∧ after = before ∧
      ∃ resultState, Carries graph.inputs graph.table (selectedFrame graph.table origin lexicalNative currentNative)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  obtain ⟨resultState, expected, history⟩ := dispatch_evaluates graph lexicalSelected currentSelected carried currentHistory valid
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic evaluated expected
  exact ⟨sameResult, sameStore, resultState, history⟩

/-- The load-based helper connects the cell receipt to the exact finite graph
transition. The source/Core body is not evaluated by this helper. -/
theorem dispatch_load {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {store : Store} {lexical : Expr}
    {position referenceIndex location : Nat} {currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word}
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (cell : CellState graph.inputs graph.table layout location currentNative currentGhost store)
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative ≠ .invalid) :
    ∃ resultState,
      Evaluates environment store (lambdaFrame graph.table layout origin lexical (.loadCell (.var referenceIndex)))
        (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)) store ∧
      Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  obtain ⟨resultState, history⟩ := selection_history graph carried cell.history valid
  exact ⟨resultState, lambdaFrame_load graph.table origin lexicalSelected reference cell.read, history⟩

/-- A completed native state result supplies the validity check itself.
The two carried parent histories are still required; decoded indices alone
are not promoted to authentication. -/
theorem dispatch_load_reflects_state {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {before after : Store} {lexical : Expr}
    {position referenceIndex location : Nat} {resultIndex : Int} {currentNative : NativeFrame}
    {lexicalGhost currentGhost : GhostFrame} {metadata : MetadataState} {origin : Word}
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (cell : CellState graph.inputs graph.table layout location currentNative currentGhost before)
    (evaluated : Evaluates environment before
      (lambdaFrame graph.table layout origin lexical (.loadCell (.var referenceIndex)))
      (encode layout (.state resultIndex)) after) :
    after = before ∧ ∃ resultState, Carries graph.inputs graph.table (.state resultIndex)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  have expected := lambdaFrame_load graph.table origin lexicalSelected reference cell.read
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic evaluated expected
  have sameFrame : (.state resultIndex : NativeFrame) =
      selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative := by
    have decoded := congrArg (decode layout) sameResult
    simpa only [decode_encode, Option.some.injEq] using decoded
  have valid : selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative ≠ .invalid := by
    rw [← sameFrame]; simp
  obtain ⟨resultState, history⟩ := selection_history graph carried cell.history valid
  exact ⟨sameStore, resultState, sameFrame.symm ▸ history⟩

theorem dispatch_load_run {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {store : Store} {lexical : Expr}
    {position referenceIndex location : Nat} {currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word}
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (cell : CellState graph.inputs graph.table layout location currentNative currentGhost store)
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative ≠ .invalid) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (lambdaFrame graph.table layout origin lexical (.loadCell (.var referenceIndex))) environment store) =
        .done (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)) store) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (lambdaFrame graph.table layout origin lexical (.loadCell (.var referenceIndex))) environment store) =
        .done actual after →
      actual = encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative) ∧ after = store) ∧
    ∃ resultState, Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  obtain ⟨resultState, evaluated, history⟩ := dispatch_load graph lexicalSelected reference carried cell valid
  exact ⟨evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ completed => evaluation_deterministic (runStateful_evaluation_sound completed) evaluated,
    resultState, history⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation
/-! Actual source-allocation annotation receipts preserve the insertion of an
indexed frame snapshot. The immediate new cell carries the same ghost metadata.
Future persistence in a completed store is a separate frame invariant; an
arbitrary child evaluation is not assumed unable to overwrite that cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation
open Core Frontend CallableIndexedHistory
open CallableAncestryPairedLookup (Inputs)
open SourceCoreCallableIndexedAllocationFrames
open DataEquality (Selects)

theorem allocator_receipt (layout : Layout) (globals : Nat) (allocate : Allocator) (request : Request)
    {code : Expr} (accepted : allocator layout globals allocate request = .ok code) :
    ∃ receipt : Annotated layout globals allocate request,
      annotateWithReceipt layout globals allocate request = .ok receipt ∧
      code = snapshotBefore layout (.var (referenceIndex globals request)) receipt.original := by
  unfold allocator at accepted
  cases prepared : annotateWithReceipt layout globals allocate request with
  | error error => simp [prepared, Except.map] at accepted
  | ok receipt =>
    simp only [prepared, Except.map, Except.ok.injEq] at accepted
    exact ⟨receipt, rfl, accepted.symm.trans receipt.exact⟩

/-- A real successful allocator callback places the exact current carrier in
an administrative cell before running the actual shifted allocation code. -/
theorem annotated_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {table : CallableAncestryPairedLookup.Table} {layout : Layout} {globals : Nat} {allocate : Allocator} {request : Request}
    (receipt : Annotated layout globals allocate request)
    {environment : Environment} {before after : Store} {result : Value} {location : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (history : Carries inputs table native ghost metadata)
    (evaluated : Evaluates (.cellRef layout.type before.length :: environment)
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native])
      (receipt.original.weakenAt 0) result after) :
    Evaluates environment before receipt.expression result after ∧
    CellState inputs table layout before.length native ghost
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native]) := by
  rw [receipt.exact]
  exact ⟨.letE (.newCell (.loadCell (.var reference) read)) evaluated,
    ⟨by simp [Store.read?], .stable history⟩⟩

/-- Completed emitted annotation exposes the actual child trace under its new
snapshot reference; this inversion does not need a source execution witness. -/
theorem annotated_reflects {layout : Layout} {globals : Nat} {allocate : Allocator} {request : Request}
    (receipt : Annotated layout globals allocate request)
    {environment : Environment} {before after : Store} {result snapshot : Value} {location : Location}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some snapshot)
    (evaluated : Evaluates environment before receipt.expression result after) :
    Evaluates (.cellRef layout.type before.length :: environment) (before ++ [snapshot])
      (receipt.original.weakenAt 0) result after := by
  rw [receipt.exact] at evaluated
  cases evaluated with
  | letE allocated body =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic allocated
      (Evaluates.newCell (.loadCell (.var reference) read))
    exact body

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedSnapshots
/-! Source allocation snapshots are protected administrative locations.
Persistence uses an explicit semantic store frame, not native typing alone.
The completed-source frame already used by general heap correspondence supplies
that contract; temporary context/global writes require a distinct location. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedSnapshots
open Core Frontend CallableAncestryPairedLookup CallableIndexedHistory GeneralHeap

structure Record where
  location : Location
  native : NativeFrame
  ghost : GhostFrame
  metadata : Option MetadataState

structure Holds {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (layout : SourceCoreCallableIndexedFrames.Layout) (mapping : LocationMap) (store : Store) (record : Record) : Prop where
  read : store.read? record.location = some (SourceCoreCallableIndexedFrames.encode layout record.native)
  administrative : record.location ∉ mapping
  history : Carries inputs table record.native record.ghost record.metadata

/-- Completed source correspondence preserves existing snapshot locations and
keeps them outside the future source-location map. -/
theorem Holds.transport {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping futureMapping : LocationMap} {before after : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record)
    (frame : AdministrativePreserved mapping before futureMapping after) :
    Holds inputs table layout futureMapping after record := by
  obtain ⟨unmapped, preserved⟩ := frame record.location snapshot.administrative
    (List.getElem?_eq_some_iff.mp snapshot.read).1
  exact ⟨preserved.trans snapshot.read, unmapped, snapshot.history⟩

theorem Holds.append {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record) (suffix : Store) :
    Holds inputs table layout mapping (before ++ suffix) record := by
  refine ⟨?_, snapshot.administrative, snapshot.history⟩
  simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp snapshot.read).1] using snapshot.read

/-- Source writes address mapped payload locations and cannot target this
snapshot. The actual write receipt supplies the store equality. -/
theorem Holds.source_write {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before after : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record) {location : Location} {value : Value}
    (mapped : location ∈ mapping) (written : before.write? location value = some after) :
    Holds inputs table layout mapping after record :=
  snapshot.transport (AdministrativePreserved.write mapped written)

/-- Mutable context or helper cells need a separate location receipt. Their
native element type is not used to infer separation from snapshot cells. -/
theorem Holds.other_write {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before after : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record) {location : Location} {value : Value}
    (different : record.location ≠ location) (written : before.write? location value = some after) :
    Holds inputs table layout mapping after record :=
  ⟨(Store.write?_preserves_other written different).trans snapshot.read, snapshot.administrative, snapshot.history⟩

/-- Fresh helper references are disjoint from every snapshot already present
in the original store, even after that store receives additional cells. -/
theorem Holds.fresh_write {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before after : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record) {suffix : Store} {offset : Nat} {value : Value}
    (written : (before ++ suffix).write? (before.length + offset) value = some after) :
    Holds inputs table layout mapping after record := by
  apply (snapshot.append suffix).other_write _ written
  have bound := (List.getElem?_eq_some_iff.mp snapshot.read).1
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))

/-- The map extension for a completed marker/payload pair cannot capture the
preceding administrative snapshot index. The initial map must already refer
to actual cells in the initial store. -/
theorem completed {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before : Store}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Carries inputs table native ghost metadata)
    (bounded : ∀ location ∈ mapping, location < before.length) (marker payload : Value) :
    Holds inputs table layout (mapping ++ [before.length + 2])
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, payload])
      ⟨before.length, native, ghost, metadata⟩ := by
  refine ⟨by simp [Store.read?], ?_, history⟩
  simp only [List.mem_append, List.mem_singleton, not_or]
  exact ⟨fun member => Nat.lt_irrefl _ (bounded _ member), by change before.length ≠ before.length + 2; omega⟩

def All {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (layout : SourceCoreCallableIndexedFrames.Layout) (mapping : LocationMap) (store : Store) (records : List Record) : Prop :=
  ∀ record ∈ records, Holds inputs table layout mapping store record

theorem All.transport {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping futureMapping : LocationMap} {before after : Store} {records : List Record}
    (snapshots : All inputs table layout mapping before records)
    (frame : AdministrativePreserved mapping before futureMapping after) :
    All inputs table layout futureMapping after records :=
  fun record member => (snapshots record member).transport frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedSnapshots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedRenaming
/-! Syntactic renaming of the finite indexed protocol. Renaming moves the
emitted scalar selectors together with their lexical slots. No claim about
exact equality of closure values or stores across an insertion is made. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedRenaming
open Core Frontend.SourceCoreCallableIndexedFrames Frontend.SourceCoreCallableIndexedDispatch
abbrev NativeFrame := Frontend.SourceCoreCallableIndexedFrames.Frame

@[simp] theorem literal (layout : Layout) (frame : NativeFrame) (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.literal layout frame).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.literal layout frame := by
  cases frame <;> rfl

@[simp] theorem plainDispatch (table : Table) (layout : Layout) (origin : Word) (lexical : Expr)
    (rows : List LambdaEdge) (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.plainDispatch table layout origin lexical rows).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.plainDispatch table layout origin (lexical.rename ξ) rows := by
  induction rows with
  | nil => rfl
  | cons edge rest ih =>
    simp only [Frontend.SourceCoreCallableIndexedDispatch.plainDispatch]
    split <;> simp only [Expr.rename, literal, ih]

@[simp] theorem viewDispatch (table : Table) (layout : Layout) (origin : Word) (id caller lexical : Expr)
    (rows : List ViewEdge) (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.viewDispatch table layout origin id caller lexical rows).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.viewDispatch table layout origin (id.rename ξ)
        (caller.rename ξ) (lexical.rename ξ) rows := by
  induction rows with
  | nil => rfl
  | cons edge rest ih =>
    simp only [Frontend.SourceCoreCallableIndexedDispatch.viewDispatch]
    split <;> simp only [Expr.rename, literal, ih]

@[simp] theorem lambdaFrame (table : Table) (layout : Layout) (origin : Word) (lexical current : Expr)
    (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin lexical current).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin
        (lexical.rename ξ) (current.rename ξ) := by
  simp [Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame, Expr.rename, Expr.renameList,
    Frontend.SourceCoreCallableIndexedFrames.invalid, Renaming.lift]

@[simp] theorem lambdaFrame_weaken (table : Table) (layout : Layout) (origin : Word) (lexical current : Expr)
    (cutoff : Nat) :
    (Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin lexical current).weakenAt cutoff =
      Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin
        (lexical.weakenAt cutoff) (current.weakenAt cutoff) := by
  simpa only [Expr.rename_insertion] using lambdaFrame table layout origin lexical current (Renaming.insertion cutoff)

@[simp] theorem readView (layout : Layout) (id target : Word) (current : Expr) (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.readView layout id target current).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.readView layout id target (current.rename ξ) := by
  simp [Frontend.SourceCoreCallableIndexedDispatch.readView, Expr.rename, Expr.renameList,
    Frontend.SourceCoreCallableIndexedFrames.invalid, Frontend.SourceCoreCallableIndexedFrames.view, Renaming.lift]

@[simp] theorem readView_weaken (layout : Layout) (id target : Word) (current : Expr) (cutoff : Nat) :
    (Frontend.SourceCoreCallableIndexedDispatch.readView layout id target current).weakenAt cutoff =
      Frontend.SourceCoreCallableIndexedDispatch.readView layout id target (current.weakenAt cutoff) := by
  simpa only [Expr.rename_insertion] using readView layout id target current (Renaming.insertion cutoff)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedRenaming
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion
/-! Completion of actual marked source allocations retains the preceding
indexed snapshot. Capture and payload expressions select the caller's existing
slots; the snapshot reference is inserted and discarded administratively.
The accepted layout and annotation receipts identify the emitted code, while
explicit lexical slot receipts identify its actual references and payload. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion
open Core Frontend SourceInference CallableIndexedHistory GeneralHeap
open SourceCoreCallableIndexedAllocationFrames

/-- Capture selection records actual lexical references in scope order. -/
inductive Captures (environment : Environment) : Renaming → SourceCoreSourceCells.Scope → Value → Prop where
  | nil {references : Renaming} : Captures environment references [] .unit
  | singleton {references : Renaming} {id : Resolved.LocalId} {type : Ty} {location : Location}
      (found : environment[references 0]? = some (.cellRef (OptionalCell.cellType type) location)) :
      Captures environment references [(id, type)] (.cellRef (OptionalCell.cellType type) location)
  | cons {references : Renaming} {id : Resolved.LocalId} {type : Ty} {location : Location}
      {next : Resolved.LocalId × Ty} {rest : SourceCoreSourceCells.Scope} {tail : Value}
      (found : environment[references 0]? = some (.cellRef (OptionalCell.cellType type) location))
      (remaining : Captures environment (fun index => references (index + 1)) (next :: rest) tail) :
      Captures environment references ((id, type) :: next :: rest) (.pair (.cellRef (OptionalCell.cellType type) location) tail)

theorem Captures.evaluates {environment : Environment} {references : Renaming} {scope : SourceCoreSourceCells.Scope} {captured : Value}
    (selected : Captures environment references scope captured) (store : Store) :
    Evaluates environment store (SourceCoreSourceCells.captures references scope) captured store := by
  induction selected with
  | nil => exact .unit
  | singleton found => exact .var found
  | cons found remaining ih => exact .pair (.var found) ih

theorem Captures.weaken {environment : Environment} {references : Renaming} {scope : SourceCoreSourceCells.Scope} {captured : Value}
    (selected : Captures environment references scope captured) (inserted : Value) :
    Captures (inserted :: environment) (fun index => references index + 1) scope captured := by
  induction selected with
  | nil => exact .nil
  | singleton found => exact .singleton (by simpa using found)
  | cons found remaining ih => exact .cons (by simpa using found) ih

/-- Actual lexical slot lookups construct capture selection; no supplied
capture evaluation is needed. Repeated locations retain their aliases. -/
theorem Captures.of_slots {environment : Environment} (scope : SourceCoreSourceCells.Scope) (references : Renaming)
    (slots : ∀ index binding, scope[index]? = some binding → ∃ location,
      environment[references index]? = some (.cellRef (OptionalCell.cellType binding.2) location)) :
    ∃ captured, Captures environment references scope captured := by
  induction scope generalizing references with
  | nil => exact ⟨.unit, .nil⟩
  | cons head rest ih =>
    obtain ⟨location, found⟩ := slots 0 head rfl
    rcases head with ⟨id, type⟩
    cases rest with
    | nil => exact ⟨_, .singleton found⟩
    | cons next tail =>
      obtain ⟨captured, selected⟩ := ih (fun index => references (index + 1)) (by
        intro index binding selected
        exact slots (index + 1) binding (by simpa using selected))
      exact ⟨_, .cons found selected⟩

/-- A fresh administrative binder shifts every actual selected slot. Its own
slot zero is absent from the shifted capture selector. -/
theorem captures_weaken (references : Renaming) (scope : SourceCoreSourceCells.Scope) :
    (SourceCoreSourceCells.captures references scope).weakenAt 0 =
      SourceCoreSourceCells.captures (fun index => references index + 1) scope := by
  induction scope generalizing references with
  | nil => simp [SourceCoreSourceCells.captures, Expr.weakenAt]
  | cons head rest ih =>
    cases rest with
    | nil => simp [SourceCoreSourceCells.captures, Expr.weakenAt]
    | cons next tail => simp only [SourceCoreSourceCells.captures, Expr.weakenAt, Nat.zero_le, ↓reduceIte, ih]

inductive PayloadAt (request : Request) (environment : Environment) : Option Value → Prop where
  | absent (shape : request.payload = none) : PayloadAt request environment none
  | initialized {value : Value} (shape : request.payload = some (.var 0))
      (found : environment[0]? = some value) : PayloadAt request environment (some value)

def optionalValue (type : Ty) : Option Value → Value
  | none => .inLeft type .unit
  | some value => .inRight .unit value

private theorem allocate_weaken (layout : SourceCoreHeapMarkers.Layout) (type : Ty) (captures : Expr) :
    (SourceCoreHeapMarkers.allocate layout type captures).weakenAt 0 =
      SourceCoreHeapMarkers.allocate layout type (captures.weakenAt 0) := by
  simp [SourceCoreHeapMarkers.allocate, SourceCoreHeapMarkers.marker, OptionalCell.allocate, Expr.weakenAt]

private theorem allocateInitialized_rename (layout : SourceCoreHeapMarkers.Layout) (type : Ty)
    (captures initializer : Expr) (ξ : Renaming) :
    (SourceCoreHeapMarkers.allocateInitialized layout type captures initializer).rename ξ =
      SourceCoreHeapMarkers.allocateInitialized layout type (captures.rename ξ) (initializer.rename ξ) := by
  simp [SourceCoreHeapMarkers.allocateInitialized, SourceCoreHeapMarkers.marker,
    OptionalCell.allocateInitialized, Expr.rename, Renaming.lift]

private theorem allocateInitialized_weaken (layout : SourceCoreHeapMarkers.Layout) (type : Ty)
    (captures initializer : Expr) :
    (SourceCoreHeapMarkers.allocateInitialized layout type captures initializer).weakenAt 0 =
      SourceCoreHeapMarkers.allocateInitialized layout type (captures.weakenAt 0) (initializer.weakenAt 0) := by
  simpa only [Expr.rename_insertion] using allocateInitialized_rename layout type captures initializer (Renaming.insertion 0)

/-- Actual success of the composed allocator provides both sealed receipts,
with the original expression shared by the layout and snapshot annotation. -/
theorem accepted_receipts {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {layout : Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) {code : Expr}
    (accepted : allocator layout globals (layouts.allocatorAt owner active onError) request = .ok code) :
    ∃ (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
      (annotation : Annotated layout globals (layouts.allocatorAt owner active onError) request),
      annotation.original = allocation.expression ∧ code = annotation.expression := by
  obtain ⟨annotation, _, exactCode⟩ := CallableIndexedAllocation.allocator_receipt _ _ _ _ accepted
  have original := annotation.allocated
  have allocated : SourceCoreAllocationLayouts.allocate layouts owner active request = .ok annotation.original := by
    cases result : SourceCoreAllocationLayouts.allocate layouts owner active request with
    | error error => simp [SourceCoreAllocationLayouts.Prepared.allocatorAt, result, Except.mapError] at original
    | ok expression =>
      have same : expression = annotation.original := by
        simpa [SourceCoreAllocationLayouts.Prepared.allocatorAt, result, Except.mapError] using original
      simp only [same]
  obtain ⟨allocation, same⟩ := SourceCoreAllocationLayouts.allocate_receipt allocated
  exact ⟨allocation, annotation, same.symm, exactCode.trans annotation.exact.symm⟩

/-- Actual layout and annotation receipts close the allocation child execution.
The only value inputs are the existing lexical references and an optional
already-evaluated result slot, as emitted by the common source-cell helpers. -/
theorem evaluates {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : Request} {layout : Layout} {globals : Nat} {allocate : Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : Annotated layout globals allocate request) (same : annotation.original = allocation.expression)
    {environment : Environment} {before : Store} {location : Location} {native : NativeFrame} {captured : Value} {payload : Option Value}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (captures : Captures environment request.references request.scope captured)
    (payloadAt : PayloadAt request environment payload) :
    Evaluates environment before annotation.expression
      (.cellRef (OptionalCell.cellType request.payloadType) (before.length + 2))
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  rw [annotation.exact, same, allocation.expressionExact]
  apply Evaluates.letE (.newCell (.loadCell (.var reference) read))
  cases payloadAt with
  | absent shape =>
    simp only [SourceCoreAllocationLayouts.allocation, shape, allocate_weaken, captures_weaken, optionalValue]
    simpa [List.append_assoc, Nat.add_assoc] using
      (SourceCoreHeapMarkers.allocate_evaluates
        ((captures.weaken (.cellRef layout.type before.length)).evaluates
          (before ++ [SourceCoreCallableIndexedFrames.encode layout native])))
  | @initialized value shape found =>
    simp only [SourceCoreAllocationLayouts.allocation, shape, allocateInitialized_weaken, optionalValue]
    have init : Evaluates (.cellRef layout.type before.length :: environment)
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native]) ((Expr.var 0).weakenAt 0) value
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native]) := by
      simpa [Expr.weakenAt] using (Evaluates.var (index := 1) (by simpa using found))
    have selected := ((captures.weaken (.cellRef layout.type before.length)).weaken value).evaluates
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native])
    rw [← captures_weaken, ← captures_weaken] at selected
    simpa [List.append_assoc, Nat.add_assoc] using
      SourceCoreHeapMarkers.allocateInitialized_evaluates init selected

/-- Any completed run of the authenticated allocation has exactly the three
new cells established above. No child execution is a premise of this result. -/
theorem reflects {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : Request} {layout : Layout} {globals : Nat} {allocate : Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : Annotated layout globals allocate request) (same : annotation.original = allocation.expression)
    {environment : Environment} {before after : Store} {location : Location} {native : NativeFrame}
    {captured result : Value} {payload : Option Value}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (captures : Captures environment request.references request.scope captured)
    (payloadAt : PayloadAt request environment payload)
    (evaluated : Evaluates environment before annotation.expression result after) :
    result = .cellRef (OptionalCell.cellType request.payloadType) (before.length + 2) ∧
      after = before ++ [SourceCoreCallableIndexedFrames.encode layout native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload] :=
  evaluation_deterministic evaluated (evaluates allocation annotation same reference read captures payloadAt)

/-- The emitted append pattern preserves every old administrative cell, while
only the payload location joins the source mapping. -/
theorem allocation_frame (mapping : LocationMap) (before : Store) (snapshot marker payload : Value) :
    AdministrativePreserved mapping before (mapping ++ [before.length + 2]) (before ++ [snapshot, marker, payload]) := by
  intro location absent bound
  refine ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨absent, Nat.ne_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))⟩
  · exact List.getElem?_append_left bound

/-- Whole allocation completion appends a protected snapshot record and
transports every existing one. The source map receives only the payload cell.
All child evaluation is derived from actual allocator/capture/slot receipts. -/
theorem preserves {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : Request} {layout : Layout} {globals : Nat} {allocate : Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : Annotated layout globals allocate request) (same : annotation.original = allocation.expression)
    {environment : Environment} {before : Store} {location : Location} {native : NativeFrame} {ghost : GhostFrame}
    {metadata : Option MetadataState} {mapping : LocationMap} {records : List CallableIndexedSnapshots.Record} {payload : Option Value}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (history : Carries graph.inputs graph.table native ghost metadata)
    (bounded : ∀ location ∈ mapping, location < before.length)
    (snapshots : CallableIndexedSnapshots.All graph.inputs graph.table layout mapping before records)
    (slots : ∀ index binding, request.scope[index]? = some binding → ∃ location,
      environment[request.references index]? = some (.cellRef (OptionalCell.cellType binding.2) location))
    (payloadAt : PayloadAt request environment payload) :
    ∃ captured,
      Evaluates environment before annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (before.length + 2))
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      AdministrativePreserved mapping before (mapping ++ [before.length + 2])
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      CallableIndexedSnapshots.All graph.inputs graph.table layout (mapping ++ [before.length + 2])
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload])
        (records ++ [⟨before.length, native, ghost, metadata⟩]) := by
  obtain ⟨captured, selected⟩ := Captures.of_slots request.scope request.references slots
  have frame := allocation_frame mapping before (SourceCoreCallableIndexedFrames.encode layout native)
    (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured) (optionalValue request.payloadType payload)
  refine ⟨captured, evaluates allocation annotation same reference read selected payloadAt, frame, ?_⟩
  intro record member
  rcases List.mem_append.mp member with old | fresh
  · exact snapshots.transport frame record old
  · have sameRecord : record = ⟨before.length, native, ghost, metadata⟩ := List.mem_singleton.mp fresh
    subst record
    exact CallableIndexedSnapshots.completed history bounded _ _

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedCaptureEnvironment
/-! Capture slots come from the existing lexical environment, including hidden
match cells and a closure's copies of them. Administrative insertion changes
their reference indices, not their values or aliases. These facts concern the
compiler's actual capture selector; an arbitrary closure may retain additional
unused native slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedCaptureEnvironment
open Core Frontend GeneralHeap CallableIndexedAllocationCompletion

/-- An indexed scope lookup selects a typed cell reference, even when that slot
is an internal match binding with no corresponding source lexical name. -/
theorem scope_slot {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    {index : Nat} {binding : Resolved.LocalId × Ty} (found : scope[index]? = some binding) :
    ∃ target : Location, world[target]? = some (OptionalCell.cellType binding.2) ∧
      canonical[index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  induction related generalizing index with
  | nil => simp at found
  | @cons scope source canonical id location target payload reference tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨target, reference.typed, rfl⟩
    | succ index => exact ih found
  | @internal scope source canonical id target payload typed absent tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨target, typed, rfl⟩
    | succ index => exact ih found

/-- Real renamed lexical references remain typed cell references; no
assumption about the types of unrelated administrative slots is needed. -/
theorem selected_slots {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual) :
    ∀ index binding, scope[index]? = some binding → ∃ target,
      world[target]? = some (OptionalCell.cellType binding.2) ∧
      actual[references index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  intro index binding found
  obtain ⟨target, typed, selected⟩ := scope_slot related found
  exact ⟨target, typed, agrees selected⟩

theorem captures {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual) :
    ∃ captured, Captures actual references scope captured := by
  apply Captures.of_slots
  intro index binding found
  obtain ⟨target, _, selected⟩ := selected_slots related agrees index binding found
  exact ⟨target, selected⟩

/-- A protected snapshot is not among the values selected by an authenticated
capture slot, even if an unrelated native environment slot holds its reference:
every selected slot is an optional cell, and the snapshot is not. -/
theorem excludes_snapshot {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual)
    {snapshot : Location} {snapshotType : Ty} (snapshotTyped : world[snapshot]? = some snapshotType)
    (notCell : ∀ payload, snapshotType ≠ OptionalCell.cellType payload)
    {index : Nat} {binding : Resolved.LocalId × Ty} (found : scope[index]? = some binding) :
    ∃ target, target ≠ snapshot ∧
      actual[references index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  obtain ⟨target, typed, selected⟩ := selected_slots related agrees index binding found
  refine ⟨target, fun same => ?_, selected⟩
  subst same
  exact notCell binding.2 (Option.some.inj (snapshotTyped.symm.trans typed))

/-- Inserting the allocation's snapshot reference leaves all selected capture
values unchanged. The general heap correspondence supplies the source slots. -/
theorem captures_inserted {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual) (inserted : Value) :
    ∃ captured, Captures actual references scope captured ∧
      Captures (inserted :: actual) (fun index => references index + 1) scope captured := by
  obtain ⟨captured, selected⟩ := captures related agrees
  exact ⟨captured, selected, selected.weaken inserted⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedCaptureEnvironment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
/-! Actual marked ordinary allocation in the common heap relation. The native
snapshot and marker extend only the typing world; the optional payload alone
extends the source-location map. The payload model must use the real complete
definition table, including administrative definitions. This does not lift an
existing smaller catalog automatically or represent generalized principal cells.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion

private theorem scope_reference {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical nativeDefinitions)
    {index : Nat} {binding : Resolved.LocalId × Ty} (found : scope[index]? = some binding) :
    ∃ target, canonical[index]? = some (.cellRef (OptionalCell.cellType binding.2) target) ∧
      world[target]? = some (OptionalCell.cellType binding.2) := by
  induction related generalizing index with
  | nil => simp at found
  | @cons scope source canonical id location target payload reference tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨target, rfl, reference.typed⟩
    | succ index => exact ih found
  | @internal scope source canonical id target payload typed absent tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨target, rfl, typed⟩
    | succ index => exact ih found

/-- Capture values and their types follow from the mapped lexical slots, not
from a supplied capture evaluation or an inspection of referenced payloads. -/
theorem captures_typed {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical nativeDefinitions)
    (agrees : EnvironmentsAgree references canonical actual) :
    ∃ captured, Captures actual references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) nativeDefinitions := by
  have slots : ∀ index binding, scope[index]? = some binding → ∃ target,
      actual[references index]? = some (.cellRef (OptionalCell.cellType binding.2) target) ∧
      world[target]? = some (OptionalCell.cellType binding.2) := by
    intro index binding found
    obtain ⟨target, selected, typed⟩ := scope_reference related found
    exact ⟨target, agrees selected, typed⟩
  clear related agrees canonical source administrative mapping
  induction scope generalizing references with
  | nil => exact ⟨.unit, .nil, .unit⟩
  | cons binding rest ih =>
    obtain ⟨id, type⟩ := binding
    obtain ⟨target, selected, typed⟩ := slots 0 (id, type) rfl
    cases rest with
    | nil => exact ⟨_, .singleton selected, .cellRef typed⟩
    | cons next tail =>
      obtain ⟨captured, selectedTail, typedTail⟩ := ih (references := fun index => references (index + 1)) (by
        intro index binding found
        exact slots (index + 1) binding (by simpa using found))
      exact ⟨_, .cons selected selectedTail, .pair (.cellRef typed) typedTail⟩

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}

/-- Two ordinary administrative allocations precede the independently
specified source allocation. World/map extensions use exact actual indices. -/
theorem heap_allocate {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    {snapshot marker payload : Value} {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType nativeDefinitions)
    (markerTyped : RuntimeValueHasType world marker markerType nativeDefinitions)
    (cell : GenericHeap.CellRepresents model mapping world
      ⟨sourceType, sourceValue, none⟩ payload payloadType)
    (allocated : Dynamic.Heap.Allocates before sourceType sourceValue sourceLocation after) :
    GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      after (store ++ [snapshot, marker, payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
        sourceLocation (store.length + 2) payloadType := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have cells := cell.extend (LocationMap.Extends.refl mapping)
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from ⟨[snapshotType, markerType], by simp⟩)
  simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using markerHeaps.allocate cells allocated

/-- The exact callback receipts, actual lexical environment and independent
ordinary source allocation imply the whole native execution and heap relation.
The source cell keeps its raw declaration type and has no generalized metadata. -/
theorem preserves_with_captures_for_type {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = nativeDefinitions)
    (frameRegistered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {sourceType : TypeSystem.Ty} {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request actual payload)
    (cell : GenericHeap.CellRepresents model mapping world
      ⟨sourceType, sourceValue, none⟩ (optionalValue request.payloadType payload) request.payloadType)
    (allocated : Dynamic.Heap.Allocates before sourceType sourceValue sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) nativeDefinitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  obtain ⟨captured, selected, typed⟩ := captures_typed environments agrees
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = SourceCoreSourceCells.captureType request.scope
    rw [allocation.keyExact]
    rfl
  have markerRegistered : allocation.entry.layout.Registered nativeDefinitions := definitions ▸ allocation.registered
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type nativeDefinitions :=
    .constructed markerRegistered.payloadLookup (captureType.symm ▸ typed)
  obtain ⟨afterHeaps, afterReference⟩ := heap_allocate heaps
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered native) markerTyped cell allocated
  exact ⟨captured, selected, typed, evaluates allocation annotation same reference read selected payloadAt,
    afterHeaps, afterReference, allocation_frame _ _ _ _ _⟩

/-- A copy of any source cell takes the same three administrative and mapped
steps as an ordinary allocation. -/
theorem heap_allocate_copy {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {copied : Dynamic.Cell} {sourceLocation : Dynamic.Location}
    {snapshot marker payload : Value} {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType nativeDefinitions)
    (markerTyped : RuntimeValueHasType world marker markerType nativeDefinitions)
    (cell : GenericHeap.CellRepresents model mapping world copied payload payloadType)
    (allocated : Dynamic.Heap.AllocatesCopy before copied sourceLocation after) :
    GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      after (store ++ [snapshot, marker, payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
        sourceLocation (store.length + 2) payloadType := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have cells := cell.extend (LocationMap.Extends.refl mapping)
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from ⟨[snapshotType, markerType], by simp⟩)
  simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using markerHeaps.allocate_copy cells allocated

/-- A closure's marked copy of a source cell: the same native execution and
heap relation as an ordinary marked allocation, with the copied cell, its
type and any principal kept. -/
theorem preserves_copy {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = nativeDefinitions)
    (frameRegistered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {copied : Dynamic.Cell} {payload : Option Value} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request actual payload)
    (cell : GenericHeap.CellRepresents model mapping world copied (optionalValue request.payloadType payload)
      request.payloadType)
    (allocated : Dynamic.Heap.AllocatesCopy before copied sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) nativeDefinitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  obtain ⟨captured, selected, typed⟩ := captures_typed environments agrees
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = SourceCoreSourceCells.captureType request.scope
    rw [allocation.keyExact]
    rfl
  have markerRegistered : allocation.entry.layout.Registered nativeDefinitions := definitions ▸ allocation.registered
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type nativeDefinitions :=
    .constructed markerRegistered.payloadLookup (captureType.symm ▸ typed)
  obtain ⟨afterHeaps, afterReference⟩ := heap_allocate_copy heaps
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered native) markerTyped cell allocated
  exact ⟨captured, selected, typed, evaluates allocation annotation same reference read selected payloadAt,
    afterHeaps, afterReference, allocation_frame _ _ _ _ _⟩

/-- Ordinary binders retain their declaration type through the same producer. -/
theorem preserves_with_captures {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = nativeDefinitions)
    (frameRegistered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request actual payload)
    (cell : GenericHeap.CellRepresents model mapping world
      ⟨request.binder.scheme.body, sourceValue, none⟩ (optionalValue request.payloadType payload) request.payloadType)
    (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) nativeDefinitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  exact preserves_with_captures_for_type allocation annotation same definitions frameRegistered
    environments agrees heaps reference read payloadAt cell allocated

/-- The compatibility result forgets only the exact captured value receipts.
The common producer retains them for snapshot registration. -/
theorem preserves {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = nativeDefinitions)
    (frameRegistered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request actual payload)
    (cell : GenericHeap.CellRepresents model mapping world
      ⟨request.binder.scheme.body, sourceValue, none⟩ (optionalValue request.payloadType payload) request.payloadType)
    (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after) :
    ∃ captured,
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  obtain ⟨captured, _, _, evaluated, finalHeaps, finalReference, frame⟩ :=
    preserves_with_captures allocation annotation same definitions frameRegistered
      environments agrees heaps reference read payloadAt cell allocated
  exact ⟨captured, evaluated, finalHeaps, finalReference, frame⟩

/-- The returned payload reference extends the lexical relation in the usual
source order; the two administrative references never become source binders. -/
theorem bind_environment {mapping : LocationMap} {world : StoreTyping}
    {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment} {store : Store}
    {sourceLocation : Dynamic.Location} {id : Resolved.LocalId}
    {snapshotType markerType payloadType : Ty}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (reference : ReferenceRepresents (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      sourceLocation (store.length + 2) payloadType) :
    DataHeap.EnvRepresents catalog (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType]) administrative
      ((id, payloadType) :: scope) ((id, sourceLocation) :: environment)
      (.cellRef (OptionalCell.cellType payloadType) (store.length + 2) :: canonical) nativeDefinitions :=
  .cons reference (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
/-! Exact transport for the emitted allocation prefix only. This fragment may
copy arbitrary existing closures as values, but never constructs or calls one.
It therefore retains exactly the same allocated values under lexical insertion.
No corresponding equality is asserted for an arbitrary function body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
open Core Frontend ReadOnly CallableIndexedAllocationCompletion

private inductive Fragment : Expr → Prop where
  | unit : Fragment .unit
  | var {index} : Fragment (.var index)
  | pair {left right} : Fragment left → Fragment right → Fragment (.pair left right)
  | construct {constructor payload} : Fragment payload → Fragment (.construct constructor payload)
  | inLeft {type payload} : Fragment payload → Fragment (.inLeft type payload)
  | inRight {type payload} : Fragment payload → Fragment (.inRight type payload)
  | newCell {type payload} : Fragment payload → Fragment (.newCell type payload)
  | loadCell {reference} : Fragment reference → Fragment (.loadCell reference)
  | letE {value body} : Fragment value → Fragment body → Fragment (.letE value body)

private theorem Fragment.rename {expression : Expr} (fragment : Fragment expression) (ξ : Renaming) :
    Fragment (expression.rename ξ) := by
  induction fragment generalizing ξ with
  | unit => exact .unit
  | var => exact .var
  | pair _ _ left right => exact .pair (left ξ) (right ξ)
  | construct _ ih => exact .construct (ih ξ)
  | inLeft _ ih => exact .inLeft (ih ξ)
  | inRight _ ih => exact .inRight (ih ξ)
  | newCell _ ih => exact .newCell (ih ξ)
  | loadCell _ ih => exact .loadCell (ih ξ)
  | letE _ _ value body => exact .letE (value ξ) (body ξ.lift)

private theorem Fragment.transport {expression : Expr} (fragment : Fragment expression)
    {environment target : Environment} {before after : Store} {result : Value} {ξ : Renaming}
    (evaluated : Evaluates environment before expression result after)
    (agrees : EnvironmentsAgree ξ environment target) :
    Evaluates target before (expression.rename ξ) result after := by
  induction fragment generalizing environment target before after result ξ with
  | unit => cases evaluated; exact .unit
  | var => cases evaluated with | var found => exact .var (agrees found)
  | pair _ _ left right =>
    cases evaluated with | pair first second => exact .pair (left first agrees) (right second agrees)
  | construct _ ih => cases evaluated with | construct payload => exact .construct (ih payload agrees)
  | inLeft _ ih => cases evaluated with | inLeft payload => exact .inLeft (ih payload agrees)
  | inRight _ ih => cases evaluated with | inRight payload => exact .inRight (ih payload agrees)
  | newCell _ ih => cases evaluated with | newCell payload => exact .newCell (ih payload agrees)
  | loadCell _ ih => cases evaluated with | loadCell reference read => exact .loadCell (ih reference agrees) read
  | letE _ _ value body =>
    cases evaluated with | letE initial tail => exact .letE (value initial agrees) (body tail (agrees.lift _))

private theorem captures_fragment (references : Renaming) (scope : SourceCoreSourceCells.Scope) :
    Fragment (SourceCoreSourceCells.captures references scope) := by
  induction scope generalizing references with
  | nil => exact .unit
  | cons head tail ih =>
    cases tail with
    | nil => exact .var
    | cons next rest => exact .pair .var (ih _)

/-- Actual allocation receipts, plus the initialized-slot shape emitted by
`SourceCells.letInitialized`, make every temporary insertion exact. -/
theorem transport {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (payloadShape : request.payload = none ∨ request.payload = some (.var 0))
    {environment target : Environment} {before after : Store} {result : Value} {ξ : Renaming}
    (evaluated : Evaluates environment before annotation.expression result after)
    (agrees : EnvironmentsAgree ξ environment target) :
    Evaluates target before (annotation.expression.rename ξ) result after := by
  have fragment : Fragment annotation.expression := by
    rw [annotation.exact, same, allocation.expressionExact]
    apply Fragment.letE (.newCell (.loadCell .var))
    rw [← Expr.rename_insertion]
    apply Fragment.rename
    rcases payloadShape with absent | initialized
    · simp only [SourceCoreAllocationLayouts.allocation, absent]
      exact .letE (.newCell (.construct (captures_fragment _ _))) (.newCell (.inLeft .unit))
    · simp only [SourceCoreAllocationLayouts.allocation, initialized]
      exact .letE .var (.letE (.newCell (.construct (by
        rw [← Expr.rename_insertion]
        exact (captures_fragment _ _).rename _))) (.newCell (.inRight .var)))
  exact fragment.transport evaluated agrees

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames
/-! Heap correspondence across the temporary callable-context write. The
context cell is source-unmapped and has a registered native frame type. A child
semantic frame is applied to the installed store; restoring the caller then
recovers preservation of every original administrative location. This uses a
semantic child contract, not a claim that arbitrary typed code avoids writes. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames
open Core Frontend GeneralHeap CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}

/-- Installing a related callable frame changes no represented source cell.
The new native carrier is typed by its registered definition independently of
the metadata-history witness carried alongside it. -/
theorem install {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {location : Location}
    {current next : NativeFrame} {currentGhost nextGhost : GhostFrame}
    (registered : layout.Registered nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (unmapped : location ∉ mapping) (typed : world[location]? = some layout.type)
    (caller : CellState inputs table layout location current currentGhost store)
    (nextHistory : Current inputs table next nextGhost) :
    GenericHeap.HeapRepresents model mapping world heap (store.set location (encode layout next)) ∧
      CellState inputs table layout location next nextGhost (store.set location (encode layout next)) := by
  have written : store.write? location (encode layout next) = some (store.set location (encode layout next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp caller.read).1, rfl⟩
  exact ⟨heaps.write_administrative (fun found => unmapped (List.mem_of_getElem? found)) typed
    (encode_runtime_typed world registered next) written, ⟨Store.write?_reads_written written, nextHistory⟩⟩

/-- A completed nested source body keeps the installed current token. Its
history is carried from entry and its value is preserved by the semantic frame. -/
theorem body_current {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping finalMap : LocationMap} {before after : Store} {location : Location}
    {native : NativeFrame} {ghost : GhostFrame}
    (unmapped : location ∉ mapping)
    (current : CellState inputs table layout location native ghost before)
    (frame : AdministrativePreserved mapping before finalMap after) :
    CellState inputs table layout location native ghost after := by
  have unchanged := (frame location unmapped (List.getElem?_eq_some_iff.mp current.read).1).2
  exact ⟨unchanged.trans current.read, current.history⟩

/-- The completed child semantic frame prevents the context cell from becoming
a source alias. Restoration preserves the represented final heap and recovers
the original caller token and the complete original administrative frame. -/
theorem restore {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {after : Dynamic.Heap} {before bodyStore : Store} {location : Location}
    {current next : NativeFrame} {currentGhost : GhostFrame}
    (registered : layout.Registered nativeDefinitions)
    (unmapped : location ∉ mapping) (typed : world[location]? = some layout.type)
    (caller : CellState inputs table layout location current currentGhost before)
    (heaps : GenericHeap.HeapRepresents model finalMap finalWorld after bodyStore)
    (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping (before.set location (encode layout next)) finalMap bodyStore) :
    GenericHeap.HeapRepresents model finalMap finalWorld after (bodyStore.set location (encode layout current)) ∧
      AdministrativePreserved mapping before finalMap (bodyStore.set location (encode layout current)) ∧
      CellState inputs table layout location current currentGhost (bodyStore.set location (encode layout current)) := by
  have bound := (List.getElem?_eq_some_iff.mp caller.read).1
  have installed : before.write? location (encode layout next) = some (before.set location (encode layout next)) :=
    Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩
  have finalTyped := worlds.lookup typed
  have written : bodyStore.write? location (encode layout current) = some (bodyStore.set location (encode layout current)) :=
    Store.write?_eq_some_iff.mpr ⟨heaps.runtime_hasTypes.location_lt finalTyped, rfl⟩
  have finalUnmapped := (frame location unmapped (by simpa using bound)).1
  refine ⟨heaps.write_administrative (fun found => finalUnmapped (List.mem_of_getElem? found)) finalTyped
    (encode_runtime_typed finalWorld registered current) written, ?_,
    ⟨Store.write?_reads_written written, caller.history⟩⟩
  intro other absent oldBound
  obtain ⟨stillAbsent, unchanged⟩ := frame other absent (by simpa using oldBound)
  refine ⟨stillAbsent, ?_⟩
  by_cases same : other = location
  · subst other
    exact (Store.write?_reads_written written).trans caller.read.symm
  · exact (Store.write?_preserves_other written same).trans
      (unchanged.trans (Store.write?_preserves_other installed same))

/-- Protected snapshots remain valid while the temporary context is installed
when their actual locations are distinct. Full closure environments may still
retain unused references; this is a store contract over selected locations. -/
theorem install_snapshots {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping : LocationMap} {store : Store} {location : Location}
    {current next : NativeFrame} {currentGhost : GhostFrame} {records : List CallableIndexedSnapshots.Record}
    (caller : CellState inputs table layout location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All inputs table layout mapping store records)
    (distinct : ∀ record ∈ records, record.location ≠ location) :
    CallableIndexedSnapshots.All inputs table layout mapping (store.set location (encode layout next)) records := by
  intro record member
  exact (snapshots record member).other_write (distinct record member)
    (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp caller.read).1, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedEntry
/-! Finite indexed lambda entry and restoration in the actual administrative
binder layout. The child body runs in its emitted environment and store.
These compositional laws preserve carried metadata; they do not supply the
source/Core body correspondence or authenticate arbitrary native closures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedEntry
open Core Frontend CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch
open DataEquality (Selects)

private theorem installed_history {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : SourceCoreCallableIndexedDispatch.Table}
    {layout : Layout} {location : Location} {before : Store} {saved : Value} {native : NativeFrame} {ghost : GhostFrame}
    (read : before.read? location = some saved) (history : Current inputs table native ghost) :
    CellState inputs table layout location native ghost (before.set location (encode layout native)) := by
  have written : before.write? location (encode layout native) = some (before.set location (encode layout native)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
  exact ⟨Store.write?_reads_written written, history⟩

/-- The exact selector after the caller frame has been saved. The syntactic
insertion law shifts emitted code using its exact insertion receipt. -/
theorem lambda_next_evaluates {layout : Layout} {environment : Environment} {before : Store}
    {referenceIndex location position : Nat} {current : NativeFrame}
    (table : SourceCoreCallableIndexedDispatch.Table) (origin : Word)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (lexicalSelected : environment[1]? = some (encode layout (.state (Int.ofNat position))))
    (read : before.read? location = some (encode layout current)) :
    Evaluates (encode layout current :: environment) before
      ((lambdaFrame table layout origin (.var 1) (.loadCell (.var referenceIndex))).weakenAt 0)
      (encode layout (selectedFrame table origin (.state (Int.ofNat position)) current)) before := by
  rw [CallableIndexedRenaming.lambdaFrame_weaken]
  simp only [Expr.weakenAt, Nat.zero_le, ↓reduceIte]
  exact CallableIndexedProtocol.lambdaFrame_load table origin (.var lexicalSelected)
    (by simpa using reference) read

/-- Entry uses the caller's actual current token and the lambda's independently
captured lexical token, then restores the caller even on language failure. -/
theorem lambda_body_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {origin : Word} {referenceIndex location position : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before after : Store}
    {current : NativeFrame} {lexicalGhost currentGhost : GhostFrame} {metadata : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState graph.inputs graph.table layout location current currentGhost before)
    (lexical : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) current ≠ .invalid)
    (bodyEvaluation : Evaluates
      (.unit :: encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: environment)
      (before.set location (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result after) :
    ∃ resultState,
      Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) current)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) ∧
      CellState graph.inputs graph.table layout location (selectedFrame graph.table origin (.state (Int.ofNat position)) current)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost)
        (before.set location (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current))) ∧
      Evaluates (argument :: encode layout (.state (Int.ofNat position)) :: environment) before
        (withFrame (.var (referenceIndex + 2))
          (lambdaFrame graph.table layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
        result (after.set location (encode layout current)) ∧
      CellState graph.inputs graph.table layout location current currentGhost (after.set location (encode layout current)) := by
  have selected : Selects (argument :: encode layout (.state (Int.ofNat position)) :: environment)
      (.var (referenceIndex + 2)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  have next := lambda_next_evaluates (referenceIndex := referenceIndex + 2) graph.table origin
    (by simpa [Nat.add_assoc] using reference)
    (show (argument :: encode layout (.state (Int.ofNat position)) :: environment)[1]? =
      some (encode layout (.state (Int.ofNat position))) from rfl) caller.read
  have evaluated := CallableContextFrames.withFrame_evaluates selected caller.read next bodyEvaluation
  obtain ⟨resultState, carried⟩ := selection_history graph lexical caller.history valid
  exact ⟨resultState, carried, installed_history caller.read (.stable carried), evaluated,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluated).1, caller.history⟩⟩

/-- Inversion exposes the real child trace and preserves the restored caller.
The completed native wrapper is the only body-execution premise. -/
theorem lambda_body_reflects {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {origin : Word} {referenceIndex location position : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before finalStore : Store}
    {current : NativeFrame} {lexicalGhost currentGhost : GhostFrame} {metadata : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState graph.inputs graph.table layout location current currentGhost before)
    (lexical : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) current ≠ .invalid)
    (evaluation : Evaluates (argument :: encode layout (.state (Int.ofNat position)) :: environment) before
      (withFrame (.var (referenceIndex + 2))
        (lambdaFrame graph.table layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1)) result finalStore) :
    (∃ resultState, Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) current)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState)) ∧
    (∃ bodyStore, Evaluates (.unit :: encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: environment)
      (before.set location (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location (encode layout current)) ∧
    CellState graph.inputs graph.table layout location current currentGhost finalStore := by
  have selected : Selects (argument :: encode layout (.state (Int.ofNat position)) :: environment)
      (.var (referenceIndex + 2)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  obtain ⟨installed, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects selected caller.read evaluation
  have expected := lambda_next_evaluates (referenceIndex := referenceIndex + 2) graph.table origin
    (by simpa [Nat.add_assoc] using reference)
    (show (argument :: encode layout (.state (Int.ofNat position)) :: environment)[1]? =
      some (encode layout (.state (Int.ofNat position))) from rfl) caller.read
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation expected
  exact ⟨selection_history graph lexical caller.history valid, ⟨bodyStore, bodyEvaluation, finalEq⟩,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluation).1, caller.history⟩⟩

/-- A named entry uses the real named cache row and restores whichever stable
or transient token was active at the call site. -/
theorem named_body_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {origin : Word} {position : Nat} {reference body : Expr}
    {environment : Environment} {result : Value} {before after : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame}
    (selected : graph.table.namedAt? origin = some position)
    (referenceSelected : Selects environment reference (.cellRef layout.type location))
    (caller : CellState graph.inputs graph.table layout location current currentGhost before)
    (bodyEvaluation : Evaluates (.unit :: encode layout current :: environment)
      (before.set location (encode layout (namedFrame graph.table origin)))
      ((body.weakenAt 0).weakenAt 0) result after) :
    ∃ metadata,
      Carries graph.inputs graph.table (namedFrame graph.table origin) (.named origin) (some metadata) ∧
      CellState graph.inputs graph.table layout location (namedFrame graph.table origin) (.named origin)
        (before.set location (encode layout (namedFrame graph.table origin))) ∧
      Evaluates environment before (withFrame reference (literal layout (namedFrame graph.table origin)) body)
        result (after.set location (encode layout current)) ∧
      CellState graph.inputs graph.table layout location current currentGhost (after.set location (encode layout current)) := by
  have next : Evaluates (encode layout current :: environment) before
      ((literal layout (namedFrame graph.table origin)).weakenAt 0)
      (encode layout (namedFrame graph.table origin)) before := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates layout _ _ _
  have evaluated := CallableContextFrames.withFrame_evaluates referenceSelected caller.read next bodyEvaluation
  obtain ⟨metadata, history⟩ := named_history graph selected
  exact ⟨metadata, history, installed_history caller.read (.stable history), evaluated,
    ⟨(CallableContextFrames.withFrame_restores referenceSelected caller.read evaluated).1, caller.history⟩⟩

/-- An instantiated read wrapper installs its captured read-time caller, even
when its eventual calling context differs. The underlying payload's execution
is the explicit child trace in the wrapper's actual administrative context. -/
theorem view_body_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {id target : Word} {position referenceIndex location : Nat}
    {environment : Environment} {argument original result : Value} {before after : Store}
    {current : NativeFrame} {readerGhost currentGhost : GhostFrame} {metadata : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState graph.inputs graph.table layout location current currentGhost before)
    (reader : Carries graph.inputs graph.table (.state (Int.ofNat position)) readerGhost (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs metadata id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs metadata id target = .ok read)
    (bodyEvaluation : Evaluates
      (.unit :: encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: original :: environment)
      (before.set location (encode layout (.view id target (Int.ofNat position))))
      (((Expr.apply (.second (.first (.var 2))) (.var 0)).weakenAt 0).weakenAt 0) result after) :
    CellState graph.inputs graph.table layout location (.view id target (Int.ofNat position)) (.view id target readerGhost)
      (before.set location (encode layout (.view id target (Int.ofNat position)))) ∧
    Evaluates (argument :: encode layout (.state (Int.ofNat position)) :: original :: environment) before
      (withFrame (.var (referenceIndex + 3)) (readView layout id target (.var 1))
        (.apply (.second (.first (.var 2))) (.var 0))) result (after.set location (encode layout current)) ∧
    CellState graph.inputs graph.table layout location current currentGhost (after.set location (encode layout current)) := by
  have selected : Selects (argument :: encode layout (.state (Int.ofNat position)) :: original :: environment)
      (.var (referenceIndex + 3)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  have next : Evaluates
      (encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: original :: environment) before
      ((readView layout id target (.var 1)).weakenAt 0)
      (encode layout (.view id target (Int.ofNat position))) before := by
    rw [CallableIndexedRenaming.readView_weaken]
    simpa only [Expr.weakenAt, Nat.zero_le, ↓reduceIte, readFrame] using
      CallableIndexedContextFrames.readView_evaluates (layout := layout)
      (environment := encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: original :: environment)
      (current := .var 2) (currentFrame := .state (Int.ofNat position)) id target (.var rfl) before
  have history : Current graph.inputs graph.table (.view id target (Int.ofNat position)) (.view id target readerGhost) :=
    .reading reader read prepared
  have evaluated := CallableContextFrames.withFrame_evaluates selected caller.read next bodyEvaluation
  exact ⟨installed_history caller.read history, evaluated,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluated).1, caller.history⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
/-! Receipts for actual indexed compiler formation hooks. The emitted code and
its native descriptor are obtained from compiler success; dynamic provenance
is carried from the current administrative cell. Neither a native function type
nor a numeric state index is used to invent source closure history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
open Core Frontend SourceInference
open SourceCoreCallableIndexedAncestry
open CallableIndexedHistory

private theorem key_eq_of_beq (left right : Key) (accepted : (left == right) = true) : left = right := by
  cases left
  cases right
  delta SourceSpecialization.instBEqSpecializationKey SourceSpecialization.instBEqSpecializationKey.beq at accepted
  simp only [Bool.and_eq_true, beq_iff_eq] at accepted
  simp_all

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

theorem originId_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (accepted : originId prepared origin = .ok id) :
    prepared.graph.inputs.callable.table.idAt? origin = some id := by
  unfold originId at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted; assumption
  · cases accepted

/-- Actual successful emission retains its exact source occurrence and full
native specialization context, as well as the graph-owned dispatch table. -/
theorem expressionHook_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output) :
    ∃ origin body, prepared.graph.inputs.callable.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      context.owner = owner ∧ context.globals = base.globals ∧ source.owner = owner.declaration ∧
      output = snapshotLambda prepared.graph.table prepared.layout.frame origin
        (creationReferenceIndex context scope) parameter result body := by
  by_cases globals : (context.owner != owner || context.globals != base.globals) = true
  · simp [expressionHook, globals, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  · have checkedGlobals : (context.owner == owner) = true ∧ context.globals = base.globals := by
      simpa [bne] using globals
    have globalsEq : context.owner = owner ∧ context.globals = base.globals :=
      ⟨key_eq_of_beq _ _ checkedGlobals.1, checkedGlobals.2⟩
    cases originSelected : originId prepared (.lambda owner node.id active) with
    | error error => simp [expressionHook, globals, originSelected, bind, Except.bind] at accepted
    | ok origin =>
      have selected := originId_receipt prepared originSelected
      cases raw <;> simp only [expressionHook, globals, originSelected, pure, Except.pure, bind, Except.bind] at accepted
      all_goals try cases accepted
      next actualParameter actualResult body =>
        by_cases header : (actualParameter != parameter || actualResult != LanguageResult.resultType result) = true
        · simp [header, throw, throwThe, MonadExceptOf.throw] at accepted
        · have headerChecks : (actualParameter == parameter) = true ∧ (actualResult == LanguageResult.resultType result) = true := by
            simpa [bne] using header
          have headerEq := And.intro ((type_beq _ _).mp headerChecks.1) ((type_beq _ _).mp headerChecks.2)
          by_cases ownerEq : (source.owner != owner.declaration) = true
          · simp [header, ownerEq, throw, throwThe, MonadExceptOf.throw] at accepted
          · have sourceOwner : source.owner = owner.declaration := by simpa using ownerEq
            simp [header, ownerEq, prepared.dispatch.tableOwner] at accepted
            exact ⟨origin, body, selected, by simp only [headerEq.1, headerEq.2],
              globalsEq.1, globalsEq.2, sourceOwner, accepted.symm⟩

/-- The named hook accepts only a registered native state from its owned
metadata table; an unregistered descriptor cannot emit an entry wrapper. -/
theorem namedBody_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : namedBody prepared function body = .ok output) :
    ∃ origin index, prepared.graph.inputs.callable.table.idAt? (.named function.signature.key) = some origin ∧
      SourceCoreCallableIndexedDispatch.namedFrame prepared.graph.table origin = .state index ∧
      output = SourceCoreCallableIndexedFrames.withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) body := by
  unfold namedBody at accepted
  obtain ⟨origin, selected, accepted⟩ := CallableAncestryPairedExpansion.bind_ok accepted
  have owned := originId_receipt prepared selected
  simp only [prepared.dispatch.tableOwner] at accepted
  cases named : SourceCoreCallableIndexedDispatch.namedFrame prepared.graph.table origin with
  | empty => simp [named, throw, throwThe, MonadExceptOf.throw] at accepted
  | invalid => simp [named, throw, throwThe, MonadExceptOf.throw] at accepted
  | view id target caller => simp [named, throw, throwThe, MonadExceptOf.throw] at accepted
  | state index =>
    simp [named] at accepted
    exact ⟨origin, index, owned, named, accepted.symm⟩

theorem namedBody_history {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : namedBody prepared function body = .ok output) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named function.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      output = SourceCoreCallableIndexedFrames.withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) body := by
  obtain ⟨origin, index, owned, named, emitted⟩ := namedBody_receipt prepared accepted
  cases selected : prepared.graph.table.namedAt? origin with
  | none => simp [SourceCoreCallableIndexedDispatch.namedFrame, selected] at named
  | some position =>
    obtain ⟨metadata, history⟩ := named_history prepared.graph selected
    exact ⟨origin, index, metadata, owned, named ▸ history, emitted⟩

/-- The indexed closure captures a related lexical state before its original
lexical environment. The ghost frame is proof-only and absent from that value. -/
def LambdaSnapshot {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    (layout : SourceCoreCallableIndexedFrames.Layout) (origin : Word) (referenceIndex : Nat)
    (parameter result : Ty) (body : Expr) (environment : Environment) (value : Value) : Prop :=
  ∃ (native : NativeFrame) (ghost : GhostFrame) (metadata : MetadataState),
    Carries graph.inputs graph.table native ghost (some metadata) ∧
    value = .closure parameter (LanguageResult.resultType result)
      (SourceCoreCallableIndexedFrames.withFrame (.var (referenceIndex + 2))
        (SourceCoreCallableIndexedDispatch.lambdaFrame graph.table layout origin (.var 1)
          (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
      (SourceCoreCallableIndexedFrames.encode layout native :: environment)

theorem expressionHook_history {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output)
    {environment : Environment} {store : Store} {location : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : MetadataState}
    (reference : environment[creationReferenceIndex context scope]? = some (.cellRef prepared.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.layout.frame native))
    (history : Carries prepared.graph.inputs prepared.graph.table native ghost (some metadata)) :
    ∃ origin body value, prepared.graph.inputs.callable.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      Evaluates environment store output value store ∧
      LambdaSnapshot prepared.graph prepared.layout.frame origin (creationReferenceIndex context scope)
        parameter result body environment value := by
  obtain ⟨origin, body, selected, rawShape, _, _, _, rfl⟩ := expressionHook_receipt prepared accepted
  exact ⟨origin, body, _, selected, rawShape, snapshotLambda_evaluates prepared.graph.table origin reference read,
    native, ghost, metadata, history, rfl⟩

theorem expressionHook_reflects {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output)
    {environment : Environment} {before after : Store} {location : Location} {value : Value}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : MetadataState}
    (reference : environment[creationReferenceIndex context scope]? = some (.cellRef prepared.layout.frame.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.layout.frame native))
    (history : Carries prepared.graph.inputs prepared.graph.table native ghost (some metadata))
    (evaluated : Evaluates environment before output value after) :
    after = before ∧ ∃ origin body,
      prepared.graph.inputs.callable.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      LambdaSnapshot prepared.graph prepared.layout.frame origin (creationReferenceIndex context scope)
        parameter result body environment value := by
  obtain ⟨origin, body, expected, selected, rawShape, expectedEval, snapshot⟩ :=
    expressionHook_history prepared accepted reference read history
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated expectedEval
  exact ⟨rfl, origin, body, selected, rawShape, snapshot⟩

/-- Successful local-read lowering either preserves an unwrapped value, or
emits the exact indexed wrapper selected by the real static view receipt. -/
theorem lowerView_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {source : TypedSource} {scope : Scope} {read : ExpressionId}
    {original output : SourceCoreBasic.LoweredExpr}
    (accepted : lowerView prepared owner active source scope read original = .ok output) :
    ∃ receipt : SourceCoreCallableViewLowering.Viewed prepared.views owner active read original,
      SourceCoreCallableViewLowering.lowerWithReceipt prepared.views owner active source read original = .ok receipt ∧
      ((receipt.entry.view.wrapsPrincipal = false ∧ output = original) ∨
        (receipt.entry.view.wrapsPrincipal = true ∧ ∃ candidate target parameter result,
          receipt.entry.view.selectedInstance = some candidate ∧
          prepared.graph.inputs.callable.table.idAt?
            (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution) = some target ∧
          original.type = CallableContract.functionType parameter result ∧
          output = {original with expression := (viewLower prepared.layout.frame parameter result receipt.entry.id target
            (scope.length + 1 + base.globals.length) original.expression)})) := by
  cases receiptResult : SourceCoreCallableViewLowering.lowerWithReceipt prepared.views owner active source read original with
  | error error => simp [lowerView, receiptResult, Except.mapError, bind, Except.bind] at accepted
  | ok receipt =>
    refine ⟨receipt, rfl, ?_⟩
    cases wraps : receipt.entry.view.wrapsPrincipal with
    | false =>
      simp [lowerView, receiptResult, wraps, Except.mapError, bind, Except.bind] at accepted
      exact Or.inl ⟨rfl, accepted.symm⟩
    | true =>
      apply Or.inr
      refine ⟨rfl, ?_⟩
      cases candidateResult : receipt.entry.view.selectedInstance with
      | none => simp [lowerView, receiptResult, wraps, candidateResult, Except.mapError, bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at accepted
      | some candidate =>
        cases targetResult : originId prepared
            (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution) with
        | error error => simp [lowerView, receiptResult, wraps, candidateResult, targetResult, Except.mapError,
            bind, Except.bind, pure, Except.pure] at accepted
        | ok target =>
          have targetOwned := originId_receipt prepared targetResult
          simp only [lowerView, receiptResult, wraps, candidateResult, targetResult, Except.mapError, bind, Except.bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at accepted
          split at accepted
          · next parameter result header =>
            cases accepted
            exact ⟨candidate, target, parameter, result, rfl, targetOwned, header, rfl⟩
          · cases accepted

/-- The exact wrapper selected by lowerView_receipt captures its related
read-time caller independently of the passed-through original payload.
Authenticating the original payload is a separate lambda-formation receipt. -/
theorem viewLower_history {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {environment : Environment} {before after : Store} {readCode : Expr}
    {parameter result : Ty} {id target descriptor : Word} {referenceIndex location : Nat}
    {identity originalPayload : Value} {caller : NativeFrame} {callerGhost : GhostFrame} {metadata : MetadataState}
    (history : Carries prepared.graph.inputs prepared.graph.table caller callerGhost (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read prepared.graph.inputs metadata id target)
    (readPrepared : SourceCoreCallableAncestryReadRecipes.prepareRead prepared.graph.inputs metadata id target = .ok read)
    (evaluated : Evaluates environment before readCode
      (.inRight .word (.pair (.pair identity originalPayload) (.word descriptor))) after)
    (reference : environment[referenceIndex]? = some (.cellRef prepared.layout.frame.type location))
    (snapshot : after.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.layout.frame caller)) :
    Evaluates environment before (viewLower prepared.layout.frame parameter result id target referenceIndex readCode)
      (.inRight .word (.pair (.pair identity
        (.closure parameter (LanguageResult.resultType result) (viewBody prepared.layout.frame id target referenceIndex)
          (SourceCoreCallableIndexedFrames.encode prepared.layout.frame caller ::
            .pair (.pair identity originalPayload) (.word descriptor) :: environment))) (.word descriptor))) after ∧
    Current prepared.graph.inputs prepared.graph.table
      (SourceCoreCallableIndexedDispatch.readFrame id target caller) (.view id target callerGhost) :=
  ⟨viewLower_evaluates evaluated reference snapshot, read_history history read readPrepared⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedCellAllocation
/-! The emitted snapshot, marker and payload allocations share one proof for
ordinary cells and generalized descriptors. Only the payload allocation extends
the Source location map; both administrative cells retain their actual values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedCellAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion

inductive SourceStep : Dynamic.Heap → Dynamic.Cell → Dynamic.Location → Dynamic.Heap → Prop where
  | ordinary {before after : Dynamic.Heap} {type : TypeSystem.Ty}
      {value : Option Dynamic.Value} {location : Dynamic.Location}
      (allocated : Dynamic.Heap.Allocates before type value location after) :
      SourceStep before ⟨type, value, none⟩ location after
  | generalized {before after : Dynamic.Heap} {function : Dynamic.GeneralizedClosure}
      {location : Dynamic.Location}
      (allocated : Dynamic.Heap.AllocatesGeneralized before function location after) :
      SourceStep before ⟨function.binder.scheme.body, none, some function⟩ location after

theorem SourceStep.metadata {before after : Dynamic.Heap} {cell : Dynamic.Cell}
    {location : Dynamic.Location} (step : SourceStep before cell location after) :
    Dynamic.HeapMetadataExtend before after := by
  cases step with
  | ordinary allocated => exact .of_allocation allocated
  | generalized allocated => exact .of_generalized_allocation allocated

variable {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment}
  {model : GenericHeap.CellModel nativeDefinitions}

/-- Exact native indices are shared by both genuine Source allocation rules. -/
theorem heap_allocate {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {sourceCell : Dynamic.Cell}
    {sourceLocation : Dynamic.Location} {snapshot marker payload : Value}
    {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.CellHeapRepresents model mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType nativeDefinitions)
    (markerTyped : RuntimeValueHasType world marker markerType nativeDefinitions)
    (cell : model.Represents mapping world sourceCell payload payloadType)
    (allocated : SourceStep before sourceCell sourceLocation after) :
    GenericHeap.CellHeapRepresents model (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      after (store ++ [snapshot, marker, payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
        sourceLocation (store.length + 2) payloadType := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative
    (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have represented := model.extend cell (LocationMap.Extends.refl mapping)
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from
      ⟨[snapshotType, markerType], by simp⟩)
  cases allocated with
  | ordinary allocated =>
      simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using
        markerHeaps.allocate_ordinary represented allocated
  | generalized allocated =>
      simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using
        markerHeaps.allocate_generalized represented allocated

/-- Actual allocator receipts and mapped capture slots supply the full emitted
execution; the Source allocation decides the kind of the newly stored cell. -/
theorem preserves_with_captures {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = nativeDefinitions)
    (frameRegistered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {sourceCell : Dynamic.Cell} {payload : Option Value} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.CellHeapRepresents model mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request actual payload)
    (cell : model.Represents mapping world sourceCell (optionalValue request.payloadType payload) request.payloadType)
    (allocated : SourceStep before sourceCell sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) nativeDefinitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      GenericHeap.CellHeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  obtain ⟨captured, selected, typed⟩ := CallableIndexedOrdinaryAllocation.captures_typed environments agrees
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = SourceCoreSourceCells.captureType request.scope
    rw [allocation.keyExact]
    rfl
  have markerRegistered : allocation.entry.layout.Registered nativeDefinitions := definitions ▸ allocation.registered
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type nativeDefinitions :=
    .constructed markerRegistered.payloadLookup (captureType.symm ▸ typed)
  obtain ⟨afterHeaps, afterReference⟩ := heap_allocate heaps
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered native) markerTyped cell allocated
  exact ⟨captured, selected, typed, evaluates allocation annotation same reference read selected payloadAt,
    afterHeaps, afterReference, allocation_frame _ _ _ _ _⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedCellAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
/-! The full indexed compiler's owned preparation receipts determine the
actual base/frame/marker definition prefix. Source catalog identities remain
unchanged, and no arbitrary full environment is identified with the base.
This is a static layout certificate, not source closure authentication. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem codebook_ambient {ambient : DataEnvironment}
    {inventories : List SourceCoreAllocationCodebook.ContextInventory} {first : Nat}
    {prepared : SourceCoreAllocationCodebook.Prepared}
    (accepted : SourceCoreAllocationCodebook.prepare ambient inventories first = .ok prepared) :
    prepared.ambient = ambient := by
  unfold SourceCoreAllocationCodebook.prepare at accepted
  split at accepted
  · obtain ⟨_, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨_, _, accepted⟩ := bind_ok accepted
      split at accepted
      · cases accepted; rfl
      · split at accepted
        · cases accepted
        · split at accepted <;> cases accepted
    · cases accepted
  · cases accepted

theorem discovery_ambient {ambient : DataEnvironment}
    {contexts : List SourceCoreAllocationDiscovery.Context} {first : Nat}
    {prepared : SourceCoreAllocationDiscovery.Prepared}
    (accepted : SourceCoreAllocationDiscovery.prepare ambient contexts first = .ok prepared) :
    prepared.ambient = ambient := by
  unfold SourceCoreAllocationDiscovery.prepare at accepted
  have extract {α β ε : Type} (f : α → β) {input : Except ε α} {output : β}
      (accepted : input.map f = .ok output) : ∃ value, input = .ok value ∧ f value = output := by
    cases input with
    | error => cases accepted
    | ok value => exact ⟨value, rfl, Except.ok.inj accepted⟩
  obtain ⟨codebook, generated, same⟩ := extract _ accepted
  subst prepared
  exact codebook_ambient generated

theorem ancestry_ambient {ambient : DataEnvironment} {layout : SourceCoreCallableIndexedAncestry.Layout}
    (accepted : SourceCoreCallableIndexedAncestry.Layout.prepare ambient = .ok layout) :
    layout.ambient = ambient := by
  unfold SourceCoreCallableIndexedAncestry.Layout.prepare at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

theorem layouts_ambient {initial : SourceCoreAllocationDiscovery.Prepared} {fuel : Nat} {expression : Expr}
    {discovered : SourceCoreAllocationDiscovery.Discovered initial fuel expression}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    (accepted : SourceCoreAllocationLayouts.prepare discovered = .ok layouts) :
    layouts.codebook.ambient = initial.ambient := by
  unfold SourceCoreAllocationLayouts.prepare at accepted
  dsimp only at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted
        exact codebook_ambient discovered.checked
      · cases accepted
    · cases accepted
  · cases accepted

/-- The actual final environment has exactly the catalog prefix, followed by
its actual indexed-frame definition and actual source marker definitions. -/
theorem definitions_exact {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    prepared.layouts.definitions = checked.catalog.definitions ++
      (prepared.ancestry.layout.frame.definition :: prepared.layouts.entries.map (·.layout.definition)) := by
  have layouts := layouts_ambient prepared.layoutsPrepared
  have discovery := discovery_ambient prepared.discoveryPrepared
  have ancestry := ancestry_ambient prepared.ancestry.layoutPrepared
  simp only [SourceCoreAllocationLayouts.Prepared.definitions, layouts, discovery,
    SourceCoreCallableIndexedAncestry.Layout.definitions, ancestry, List.append_assoc, List.singleton_append]

def ambientDefinitions {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    AmbientDefinitions checked.catalog.definitions where
  definitions := prepared.layouts.definitions
  basePrefix := ⟨_, definitions_exact prepared⟩

@[simp] theorem ambient_definitions {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    (ambientDefinitions prepared).definitions = prepared.layouts.definitions := rfl

theorem wellFormed {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    (ambientDefinitions prepared).definitions.WellFormed := prepared.layouts.definitionsTyped

theorem base_constructor {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) {constructor : ConstructorId} {payload : Ty}
    (registered : checked.catalog.definitions.lookupConstructorPayloadType? constructor = some payload) :
    prepared.layouts.definitions.lookupConstructorPayloadType? constructor = some payload :=
  (ambientDefinitions prepared).basePrefix.constructor_lookup registered

/-- The frame is registered in the real final table independently of every
source metadata ID. Further allocation markers retain their owned indices. -/
theorem frame_registered {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    prepared.ancestry.layout.frame.Registered prepared.layouts.definitions := by
  have extension : prepared.ancestry.layout.definitions.Extends prepared.layouts.definitions := by
    refine ⟨prepared.layouts.entries.map (·.layout.definition), ?_⟩
    rw [SourceCoreAllocationLayouts.Prepared.definitions, layouts_ambient prepared.layoutsPrepared,
      discovery_ambient prepared.discoveryPrepared]
  exact ⟨extension.data_lookup prepared.ancestry.layout.registered.lookup⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceiverTables
/-! The actual indexed run retains the table rebuilt for its own raw registry.
The receipt records the existing optional base table and the exact callable
append. It does not assume decoder coverage or reorder table priorities. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceiverTables
open Core Frontend SourceInference

variable {checked : SourceCoreCompatibleCatalog.Checked}

/-- The same callable rows appended by the public indexed runner. -/
def appendCallable (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (table : SourceCoreFaultSites.Table) : SourceCoreFaultSites.Table :=
  match prepared.base.callableDiagnostics with
  | none => table
  | some diagnostics => {table with additional := table.additional ++
      diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val)}

/-- Appending disjoint rows preserves the existing decoder's exact priority. -/
theorem diagnostic_append {table : SourceCoreFaultSites.Table}
    {extra : List (Word × SourceCoreFaultSites.Diagnostic)} {token : Word}
    (disjoint : extra.find? (fun item => decide (item.1 = token)) = none) :
    ({table with additional := table.additional ++ extra}).diagnostic? token = table.diagnostic? token := by
  simp only [SourceCoreFaultSites.Table.diagnostic?, List.find?_append, disjoint]
  cases table.additional.find? (fun item => decide (item.1 = token)) <;> rfl

/-- The genuine numerical range boundary excludes only the appended callable
rows. It does not assume a decoder law for unrelated Source occurrences. -/
theorem appendCallable_diagnostic {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {callable : SourceCoreCallableFaultSites.Program} {table : SourceCoreFaultSites.Table} {token : Word}
    (present : prepared.base.callableDiagnostics = some callable)
    (below : token.val < callable.unknown.val) :
    (appendCallable prepared table).diagnostic? token = table.diagnostic? token := by
  rw [appendCallable, present]
  apply diagnostic_append
  apply List.find?_eq_none.mpr
  intro item member
  have lower := (List.mem_filter.mp member).2
  have lower' : callable.unknown.val ≤ item.1.val := of_decide_eq_true lower
  intro equalBool
  have equal : item.1 = token := of_decide_eq_true equalBool
  have same := congrArg Fin.val equal
  omega

/-- This is the actual callable-table range check, including the absent-table
case. It concerns the one issued token rather than every Source expression. -/
def BelowCallable (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (token : Word) : Prop :=
  match prepared.base.callableDiagnostics with
  | none => True
  | some callable => token.val < callable.unknown.val

theorem appendCallable_diagnostic_of_below
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {table : SourceCoreFaultSites.Table} {token : Word}
    (below : BelowCallable prepared token) :
    (appendCallable prepared table).diagnostic? token = table.diagnostic? token := by
  cases present : prepared.base.callableDiagnostics with
  | none => simp only [appendCallable, present]
  | some callable =>
    exact appendCallable_diagnostic present (by simpa only [BelowCallable, present] using below)

/-- Actual base rebuilding and exact receiver identity are separate receipts.
The absent-base alternative keeps the original public fallback unchanged. -/
def IssuedAt (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry)
    (receiver : SourceCoreFaultSites.Table) : Prop :=
  ∃ base,
    (match prepared.base.diagnostics with
    | some diagnostics => diagnostics.tableForRegistry registry extension = .ok base
    | none => base = {
        owner := entry.key.declaration
        resultType := entry.sourceResultType
        reads := []
        escapedReason := Word.zero}) ∧
    receiver = appendCallable prepared base

private def computed (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry) :
    Except SourceCoreCallableIndexedPrograms.RunError SourceCoreFaultSites.Table := do
  let table ← match prepared.base.diagnostics with
    | some diagnostics => (diagnostics.tableForRegistry registry extension).mapError SourceCoreCallableIndexedPrograms.RunError.diagnostics
    | none => pure {
        owner := entry.key.declaration
        resultType := entry.sourceResultType
        reads := []
        escapedReason := Word.zero}
  pure (appendCallable prepared table)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {map : ε → δ}
    {result : α} (accepted : action.mapError map = .ok result) : action = .ok result := by
  cases action <;> cases accepted <;> rfl

private theorem issued_of_computed
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : computed prepared entry registry extension = .ok table) :
    IssuedAt prepared entry registry extension table := by
  unfold computed at accepted
  cases present : prepared.base.diagnostics with
  | none =>
    simp only [present, pure, Except.pure, bind, Except.bind] at accepted
    cases accepted
    exact ⟨_, present ▸ rfl, rfl⟩
  | some diagnostics =>
    simp only [present] at accepted
    obtain ⟨base, rebuilt, accepted⟩ := bind_ok accepted
    cases accepted
    refine ⟨base, ?_, rfl⟩
    rw [present]
    exact mapError_ok rebuilt

/-- Finite inversion of the genuine public run exposes its own table receipt.
Encoding and native execution are not repeated; their actual returned values
remain the same completion fields. -/
theorem issued_of_runSource
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceTypedRuntime.Value}
    {fuel validationFuel : Nat} {completion : SourceCoreCallableIndexedPrograms.Completion prepared}
    (accepted : prepared.runSource key arguments fuel validationFuel = .ok completion) :
    IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics := by
  unfold SourceCoreCallableIndexedPrograms.Prepared.runSource at accepted
  cases selected : prepared.find? key with
  | none =>
    rw [selected] at accepted
    change Except.error (SourceCoreCallableIndexedPrograms.RunError.missingEntry key) = .ok completion at accepted
    cases accepted
  | some entry =>
    simp only [selected, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨encoded, _encodedBy, accepted⟩ := bind_ok accepted
    obtain ⟨body, _bodyBy, accepted⟩ := bind_ok accepted
    split at accepted
    · simp [throw] at accepted
    · obtain ⟨native, _nativeBy, accepted⟩ := bind_ok accepted
      obtain ⟨table, tableBy, accepted⟩ := bind_ok accepted
      cases accepted
      apply issued_of_computed
      exact tableBy

/-- Resuming the actual native checkpoint keeps the original raw registry
and receiver table. No diagnostic factory is run again. -/
theorem IssuedAt.resume
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {completion : SourceCoreCallableIndexedPrograms.Completion prepared}
    (receipt : IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics) (fuel : Nat) :
    IssuedAt prepared (completion.resume fuel).entry (completion.resume fuel).result.context.registry
      (completion.resume fuel).result.extension (completion.resume fuel).result.diagnostics := by
  unfold SourceCoreCallableIndexedPrograms.Completion.resume
  split <;> exact receipt

/-- The actual receiver decodes a retained ordinary read. Rebuilding uses
that completion's registry and extension, and the real table priorities
remain explicit until the authentic issuer supplies their receipts. -/
theorem read_diagnostic_of_issued
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {completion : SourceCoreCallableIndexedPrograms.Completion prepared}
    (receipt : IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program
      (SourceCoreCompatibleValues.Context.initial checked)}
    (present : prepared.base.diagnostics = some issued)
    {base : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry completion.result.context.registry
      completion.result.extension = .ok base)
    {site : SourceCoreFaultSites.ReadSite}
    (positive : site.reason ≠ Word.zero)
    (ordinary : site.reason ≠ base.escapedReason)
    (noBoundary : base.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none)
    (found : base.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site)
    (below : BelowCallable prepared site.reason) :
    completion.result.diagnostics.diagnostic? site.reason = some {
      error := .uninitializedLocal site.binder
      site := .occurrence site.expression.occurrence
      span := some site.span
    } := by
  obtain ⟨actual, actualBy, receiver⟩ := receipt
  rw [present] at actualBy
  have same : actual = base := Except.ok.inj (actualBy.symm.trans rebuilt)
  subst actual
  rw [receiver, appendCallable_diagnostic_of_below below]
  exact SourceCoreFaultSites.Table.read_diagnostic positive ordinary noBoundary found

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceiverTables
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultObservation
/-! Joint observations retain the original Source reason and reached heap,
the actual native failure token, and the exact public diagnostic. The receiver
is the existing failed-token branch of Execution.observe. These receipts do
not identify other public boundary or validation errors with Source faults,
and do not supply a category-wide FunctionCalls.FaultRep. Actual read/place
origin witnesses and their issued-table decoding remain independent inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultObservation
open Core Frontend SourceInference GeneralHeap

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {nativeProgram : SourceCoreUnifiedRuntime.Program checked}
  {prepared : SourceCoreUnifiedRuntime.Prepared nativeProgram}
  (execution : SourceCoreUnifiedRuntime.Execution prepared)
  {token : Word} {store : Store} {diagnostic : SourceCoreFaultSites.Diagnostic}

/-- This is the exact table carried by the actual native completion. -/
def DecodedAt (token : Word) (diagnostic : SourceCoreFaultSites.Diagnostic) : Prop :=
  execution.completion.result.diagnostics.diagnostic? token = some diagnostic

/-- A real failed observation is decoded after exporting that same completion.
The exported heap is retained literally, including the original inert prefix. -/
theorem observe_failed {exportFuel : Option Nat}
    {exported : SourceCoreCallableIndexedHeapOutputs.Export prepared.output
      execution.completion execution.initial.heap}
    (heapExport : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output
      execution.completion execution.initial.heap
      (exportFuel.getD execution.exportFuel) = .ok exported)
    (failed : execution.completion.result.native.observation = .failed token store)
    (decoded : DecodedAt execution token diagnostic) :
    execution.observe exportFuel = .ok (.fault diagnostic.error ⟨exported.heap⟩) := by
  simp only [SourceCoreUnifiedRuntime.Execution.observe, heapExport, Except.mapError,
    bind, Except.bind, failed, DecodedAt] at *
  rw [decoded]
  rfl

/-- An accepted public failure observation supplies its actual heap export
and exact diagnostic. Native failure is explicit, so successful-native deep
validation faults and initial boundary faults are not classified here. -/
theorem observe_failed_receipts {exportFuel : Option Nat}
    {error : SourceTypedRuntime.RuntimeError} {final : SourceTypedRuntime.RuntimeState}
    (failed : execution.completion.result.native.observation = .failed token store)
    (observed : execution.observe exportFuel = .ok (.fault error final)) :
    ∃ exported : SourceCoreCallableIndexedHeapOutputs.Export prepared.output
        execution.completion execution.initial.heap,
      SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output execution.completion
        execution.initial.heap (exportFuel.getD execution.exportFuel) = .ok exported ∧
      ∃ diagnostic, DecodedAt execution token diagnostic ∧ diagnostic.error = error ∧
        final = ⟨exported.heap⟩ := by
  cases exportedAt : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output
      execution.completion execution.initial.heap (exportFuel.getD execution.exportFuel) with
  | error problem =>
    simp only [SourceCoreUnifiedRuntime.Execution.observe, exportedAt, Except.mapError,
      bind, Except.bind] at observed
    cases observed
  | ok exported =>
    simp only [SourceCoreUnifiedRuntime.Execution.observe, exportedAt, Except.mapError,
      bind, Except.bind, failed] at observed
    cases decoded : execution.completion.result.diagnostics.diagnostic? token with
    | none => simp only [decoded] at observed; cases observed
    | some diagnostic =>
      simp only [decoded] at observed
      cases observed
      exact ⟨exported, rfl, diagnostic, decoded, rfl, rfl⟩

/-- The Source and native heaps are related at the original same reached
store/map/world. No Source reason or location is replaced by the public error. -/
structure Packet {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : SourceSemantics.Program) (entry : Dynamic.ProgramEntry)
    (before after : Dynamic.Heap) (reason : Dynamic.SemanticFault)
    (mapping : LocationMap) (world : StoreTyping)
    (token : Word) (store : Store) (diagnostic : SourceCoreFaultSites.Diagnostic) : Prop where
  sourceFault : Dynamic.ProgramFaults program entry before reason after
  reachedHeap : GenericHeap.HeapRepresents model mapping world after store
  nativeFault : execution.completion.result.native.observation = .failed token store
  decoded : DecodedAt execution token diagnostic

variable {catalog : SourceCoreDataCatalog.Catalog}
  {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : SourceSemantics.Program} {entry : Dynamic.ProgramEntry}
  {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
  {mapping : LocationMap} {world : StoreTyping}

/-- Genuine paired completion receipts construct the observation packet.
The diagnostic equation concerns only its actual receiver table. -/
theorem packet_of_receipts
    (sourceFault : Dynamic.ProgramFaults program entry before reason after)
    (reachedHeap : GenericHeap.HeapRepresents model mapping world after store)
    (nativeFault : execution.completion.result.native.observation = .failed token store)
    (decoded : DecodedAt execution token diagnostic) :
    Packet execution model program entry before after reason mapping world token store diagnostic :=
  ⟨sourceFault, reachedHeap, nativeFault, decoded⟩

/-- The complete joint packet survives the public decoder unchanged. An
accepted export is required; exporter errors retain their actual public type. -/
theorem Packet.observe
    (packet : Packet execution model program entry before after reason mapping world token store diagnostic)
    {exportFuel : Option Nat}
    {exported : SourceCoreCallableIndexedHeapOutputs.Export prepared.output
      execution.completion execution.initial.heap}
    (heapExport : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output
      execution.completion execution.initial.heap
      (exportFuel.getD execution.exportFuel) = .ok exported) :
    Packet execution model program entry before after reason mapping world token store diagnostic ∧
      execution.observe exportFuel = .ok (.fault diagnostic.error ⟨exported.heap⟩) :=
  ⟨packet, observe_failed execution heapExport packet.nativeFault packet.decoded⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultObservation
end
