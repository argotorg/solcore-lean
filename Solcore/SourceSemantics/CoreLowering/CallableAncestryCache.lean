import Solcore.Frontend.SourceCoreCallableAncestryCache
import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition

/-! A completed finite transition table covers every independently
authenticated metadata frame, including arbitrary repeated lambda ancestry.
The closure certificate is about named/lambda/view metadata transitions, not
source or Core execution. Constructing it from the actual reachable worklist
is a separate preparation obligation; no arbitrary traversal fuel or supplied
list of runtime frames appears in these theorems. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryCache
open Frontend SourceInference TypeSystem CallableAncestryMetadata
abbrev Table := SourceCoreCallableAncestryCache.Table
abbrev State := CallableAncestryMetadata.State

def nativeState (state : State) : SourceCoreCallableAncestryCache.State :=
  ⟨state.owner, state.active, state.source⟩

def sourceState (state : SourceCoreCallableAncestryCache.State) : State :=
  ⟨state.owner, state.active, state.source⟩

@[simp] theorem source_native (state : State) : sourceState (nativeState state) = state := rfl
@[simp] theorem native_source (state : SourceCoreCallableAncestryCache.State) : nativeState (sourceState state) = state := rfl

theorem native_injective {left right : State} (same : nativeState left = nativeState right) : left = right :=
  congrArg sourceState same

/-- Every selected row is an owned metadata transition. These are finite-row
obligations; they contain no premise that a source/Core program has executed. -/
structure Sound {checked : Checked} {base : Base checked} (owned : Owned base) (table : Table) : Prop where
  named : ∀ {id position}, table.namedAt? id = some position →
    ∃ receipt : Named owned id, table.stateAt? position = some (nativeState receipt.state)
  lambda : ∀ {position state id}, table.stateAt? position = some (nativeState state) →
    table.lambdaAllowed position id = true → ∃ receipt : LambdaAt owned id, Nonempty (LambdaSource receipt state)
  view : ∀ {position state id target destination}, table.stateAt? position = some (nativeState state) →
    table.viewAt? position id target = some destination →
      ∃ (receipt : ViewAt owned id target) (step : ViewStep receipt state),
        table.stateAt? destination = some (nativeState step.after)

/-- Closure of a completed worklist. Each matching view factory is represented
at every reached state. Lambda edges keep that exact state; named edges seed
every owned named source. No condition mentions whole recursive frames. -/
structure Closed {checked : Checked} {base : Base checked} (owned : Owned base) (table : Table) : Prop where
  named : ∀ {id} (receipt : Named owned id), ∃ position,
    table.namedAt? id = some position ∧ table.stateAt? position = some (nativeState receipt.state)
  lambda : ∀ {position state id}, table.stateAt? position = some (nativeState state) →
    ∀ (receipt : LambdaAt owned id), LambdaSource receipt state → table.lambdaAllowed position id = true
  view : ∀ {position state id target}, table.stateAt? position = some (nativeState state) →
    ∀ (receipt : ViewAt owned id target) (step : ViewStep receipt state), ∃ destination,
      table.viewAt? position id target = some destination ∧ table.stateAt? destination = some (nativeState step.after)

structure Prepared {checked : Checked} {base : Base checked} (owned : Owned base) where private mk ::
  table : Table
  sound : Sound owned table
  closed : Closed owned table

/-- Proof-facing completion boundary. Actual factory preparation must produce
both certificates before its table can use the all-frame theorem below. -/
def certify {checked : Checked} {base : Base checked} {owned : Owned base}
    (table : Table) (sound : Sound owned table) (closed : Closed owned table) : Prepared owned :=
  ⟨table, sound, closed⟩

def IndexMeaning {checked : Checked} {base : Base checked} (owned : Owned base) (table : Table)
    (frame : ContextFrame) : Option Nat → Prop
  | none => Authenticates owned frame none
  | some position => ∃ state, table.stateAt? position = some (nativeState state) ∧
      Authenticates owned frame (some state)

theorem lookupIndex_sound {checked : Checked} {base : Base checked} {owned : Owned base} {table : Table}
    (sound : Sound owned table) (frame : ContextFrame) {result : Option Nat}
    (found : table.lookupIndex? frame = some result) : IndexMeaning owned table frame result := by
  induction frame generalizing result with
  | empty => cases found; exact .empty
  | named id =>
    cases selected : table.namedAt? id with
    | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, selected] at found
    | some position =>
      simp only [SourceCoreCallableAncestryCache.Table.lookupIndex?, selected, Option.map_some, Option.some.injEq] at found
      subst result
      obtain ⟨receipt, stored⟩ := sound.named selected
      exact ⟨receipt.state, stored, .named receipt⟩
  | lambda id parent ih =>
    cases parentResult : table.lookupIndex? parent with
    | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
    | some parentIndex =>
      cases parentIndex with
      | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
      | some position =>
        simp only [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
        split at found
        · next allowed =>
          cases found
          obtain ⟨state, stored, ancestry⟩ := ih parentResult
          obtain ⟨receipt, ⟨metadata⟩⟩ := sound.lambda stored allowed
          exact ⟨state, stored, .lambda ancestry receipt metadata⟩
        · cases found
  | view id target parent ih =>
    cases parentResult : table.lookupIndex? parent with
    | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
    | some parentIndex =>
      cases parentIndex with
      | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
      | some position =>
        cases selected : table.viewAt? position id target with
        | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult, selected] at found
        | some destination =>
          simp only [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult, selected,
            Option.map_some, Option.some.injEq] at found
          subst result
          obtain ⟨state, stored, ancestry⟩ := ih parentResult
          obtain ⟨receipt, step, final⟩ := sound.view stored selected
          exact ⟨step.after, final, .view ancestry receipt step⟩

def Indexed (table : Table) (frame : ContextFrame) : Option State → Prop
  | none => table.lookupIndex? frame = some none
  | some state => ∃ position, table.lookupIndex? frame = some (some position) ∧
      table.stateAt? position = some (nativeState state)

theorem lookupIndex_complete {checked : Checked} {base : Base checked} {owned : Owned base} {table : Table}
    (closed : Closed owned table) {frame : ContextFrame} {state : Option State}
    (authenticated : Authenticates owned frame state) : Indexed table frame state := by
  induction authenticated with
  | empty => rfl
  | named receipt =>
    obtain ⟨position, selected, stored⟩ := closed.named receipt
    exact ⟨position, by simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, selected], stored⟩
  | lambda ancestry receipt metadata ih =>
    obtain ⟨position, parent, stored⟩ := ih
    have allowed := closed.lambda stored receipt metadata
    exact ⟨position, by simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parent, allowed], stored⟩
  | view ancestry receipt step ih =>
    obtain ⟨position, parent, stored⟩ := ih
    obtain ⟨destination, selected, final⟩ := closed.view stored receipt step
    exact ⟨destination, by simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parent, selected], final⟩

theorem lookup_complete {checked : Checked} {base : Base checked} {owned : Owned base} {table : Table}
    (closed : Closed owned table) {frame : ContextFrame} {state : Option State}
    (authenticated : Authenticates owned frame state) : table.lookup? frame = some (state.map nativeState) := by
  have indexed := lookupIndex_complete closed authenticated
  cases state with
  | none =>
    change table.lookupIndex? frame = some none at indexed
    simp [SourceCoreCallableAncestryCache.Table.lookup?, indexed]
  | some state =>
    obtain ⟨position, selected, stored⟩ := indexed
    simp [SourceCoreCallableAncestryCache.Table.lookup?, selected, stored]

theorem lookup_sound {checked : Checked} {base : Base checked} {owned : Owned base} {table : Table}
    (sound : Sound owned table) {frame : ContextFrame} {state : Option SourceCoreCallableAncestryCache.State}
    (found : table.lookup? frame = some state) : Authenticates owned frame (state.map sourceState) := by
  cases indexed : table.lookupIndex? frame with
  | none => simp [SourceCoreCallableAncestryCache.Table.lookup?, indexed] at found
  | some result =>
    have meaning := lookupIndex_sound sound frame indexed
    cases result with
    | none =>
      simp only [SourceCoreCallableAncestryCache.Table.lookup?, indexed, Option.some.injEq] at found
      subst state
      exact meaning
    | some position =>
      obtain ⟨selected, stored, ancestry⟩ := meaning
      simp only [SourceCoreCallableAncestryCache.Table.lookup?, indexed, stored, Option.map_some,
        Option.some.injEq] at found
      subst state
      exact ancestry

theorem Prepared.lookup_iff {checked : Checked} {base : Base checked} {owned : Owned base}
    (prepared : Prepared owned) {frame : ContextFrame} {state : Option State} :
    prepared.table.lookup? frame = some (state.map nativeState) ↔ Authenticates owned frame state := by
  constructor
  · intro found
    have authenticated := lookup_sound prepared.sound found
    cases state <;> exact authenticated
  · exact lookup_complete prepared.closed

/-- Deduplicating reached states by the frontend key preserves the full
metadata state, provided the rows came from authenticated recipes. -/
theorem native_key_injective {checked : Checked} {base : Base checked} {owned : Owned base}
    {leftFrame rightFrame : ContextFrame} {left right : SourceCoreCallableAncestryCache.State}
    (leftAuthenticated : Authenticates owned leftFrame (some (sourceState left)))
    (rightAuthenticated : Authenticates owned rightFrame (some (sourceState right)))
    (same : left.key = right.key) : left = right := by
  have converted := congrArg (fun key : SourceCoreCallableAncestryCache.Key =>
    (⟨key.owner, key.active, key.requirements⟩ : CallableAncestryProfiles.SourceComposition.StateKey)) same
  have sourceEqual := CallableAncestryProfiles.SourceComposition.stateKey_injective leftAuthenticated rightAuthenticated converted
  exact congrArg nativeState sourceEqual

theorem Prepared.lookup_key_injective {checked : Checked} {base : Base checked} {owned : Owned base}
    (prepared : Prepared owned) {leftFrame rightFrame : ContextFrame}
    {left right : SourceCoreCallableAncestryCache.State}
    (leftFound : prepared.table.lookup? leftFrame = some (some left))
    (rightFound : prepared.table.lookup? rightFrame = some (some right))
    (same : left.key = right.key) : left = right :=
  native_key_injective (lookup_sound prepared.sound leftFound) (lookup_sound prepared.sound rightFound) same

end Solcore.SourceSemantics.CoreLowering.CallableAncestryCache
