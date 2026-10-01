import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProfiles

/-! Completed paired-table lookup and the pure metadata-factory domain.
An applied view has two independent parent derivations: the read caller and
the lexical principal. Authentication here is metadata provenance, not runtime
execution history. Native snapshot/code/capture coverage is a separate layer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedLookup
open Frontend SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev State := SourceCoreCallableAncestryReadRecipes.State
abbrev Frame := SourceCoreCallablePairedFrames.Frame
abbrev Table := SourceCoreCallableAncestryPairedCache.Table

inductive Authenticates {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    Frame → Option State → Prop where
  | empty : Authenticates inputs .empty none
  | named {id : Core.Word} {state : State}
      (selected : SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state) :
      Authenticates inputs (.named id) (some state)
  | lambda {parent : Frame} {state : State} {id : Core.Word}
      (ancestry : Authenticates inputs parent (some state))
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true) :
      Authenticates inputs (.lambda id parent) (some state)
  | appliedView {callerFrame lexicalFrame : Frame} {caller lexical result : State} {id target : Core.Word}
      (callerAncestry : Authenticates inputs callerFrame (some caller))
      (lexicalAncestry : Authenticates inputs lexicalFrame (some lexical))
      (selected : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result) :
      Authenticates inputs (.appliedView id target callerFrame lexicalFrame) (some result)

structure Sound {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) : Prop where
  named : ∀ {id position}, table.namedAt? id = some position → ∃ state,
    SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state ∧ table.stateAt? position = some state
  lambda : ∀ {position state id}, table.stateAt? position = some state → table.lambdaAllowed position id = true →
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true
  view : ∀ {callerIndex lexicalIndex caller lexical id target position},
    table.stateAt? callerIndex = some caller → table.stateAt? lexicalIndex = some lexical →
    table.viewAt? callerIndex lexicalIndex id target = some position → ∃ result,
      SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result ∧
        table.stateAt? position = some result

structure Closed {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) : Prop where
  named : ∀ {id state}, SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state →
    ∃ position, table.namedAt? id = some position ∧ table.stateAt? position = some state
  lambda : ∀ {position state id}, table.stateAt? position = some state →
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true → table.lambdaAllowed position id = true
  view : ∀ {callerIndex lexicalIndex caller lexical id target result},
    table.stateAt? callerIndex = some caller → table.stateAt? lexicalIndex = some lexical →
    SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result →
    ∃ position, table.viewAt? callerIndex lexicalIndex id target = some position ∧ table.stateAt? position = some result

def IndexMeaning {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (frame : Frame) : Option Nat → Prop
  | none => Authenticates inputs frame none
  | some position => ∃ state, table.stateAt? position = some state ∧ Authenticates inputs frame (some state)

theorem lookupIndex_sound {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : Sound inputs table) (frame : Frame) {result : Option Nat}
    (found : table.lookupIndex? frame = some result) : IndexMeaning inputs table frame result := by
  induction frame generalizing result with
  | empty => cases found; exact .empty
  | named id =>
    cases selected : table.namedAt? id with
    | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, selected] at found
    | some position =>
      simp only [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, selected, Option.map_some, Option.some.injEq] at found
      subst result
      obtain ⟨state, generated, stored⟩ := sound.named selected
      exact ⟨state, stored, .named generated⟩
  | lambda id parent ih =>
    cases parentResult : table.lookupIndex? parent with
    | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, parentResult] at found
    | some parentIndex =>
      cases parentIndex with
      | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, parentResult] at found
      | some position =>
        simp only [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, parentResult] at found
        split at found
        · next allowed =>
          cases found
          obtain ⟨state, stored, ancestry⟩ := ih parentResult
          exact ⟨state, stored, .lambda ancestry (sound.lambda stored allowed)⟩
        · cases found
  | view id target parent => cases found
  | appliedView id target caller lexical callerIH lexicalIH =>
    cases callerResult : table.lookupIndex? caller with
    | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult] at found
    | some callerIndex =>
      cases callerIndex with
      | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult] at found
      | some callerPosition =>
        cases lexicalResult : table.lookupIndex? lexical with
        | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult, lexicalResult] at found
        | some lexicalIndex =>
          cases lexicalIndex with
          | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult, lexicalResult] at found
          | some lexicalPosition =>
            cases selected : table.viewAt? callerPosition lexicalPosition id target with
            | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult, lexicalResult, selected] at found
            | some position =>
              simp only [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult, lexicalResult,
                selected, Option.map_some, Option.some.injEq] at found
              subst result
              obtain ⟨callerState, callerStored, callerAncestry⟩ := callerIH callerResult
              obtain ⟨lexicalState, lexicalStored, lexicalAncestry⟩ := lexicalIH lexicalResult
              obtain ⟨state, generated, stored⟩ := sound.view callerStored lexicalStored selected
              exact ⟨state, stored, .appliedView callerAncestry lexicalAncestry generated⟩

def Indexed (table : Table) (frame : Frame) : Option State → Prop
  | none => table.lookupIndex? frame = some none
  | some state => ∃ position, table.lookupIndex? frame = some (some position) ∧ table.stateAt? position = some state

theorem lookupIndex_complete {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (closed : Closed inputs table) {frame : Frame} {state : Option State}
    (authenticated : Authenticates inputs frame state) : Indexed table frame state := by
  induction authenticated with
  | empty => rfl
  | named generated =>
    obtain ⟨position, selected, stored⟩ := closed.named generated
    exact ⟨position, by simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, selected], stored⟩
  | lambda ancestry generated ih =>
    obtain ⟨position, parent, stored⟩ := ih
    have allowed := closed.lambda stored generated
    exact ⟨position, by simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, parent, allowed], stored⟩
  | appliedView callerAncestry lexicalAncestry generated callerIH lexicalIH =>
    obtain ⟨callerIndex, callerFound, callerStored⟩ := callerIH
    obtain ⟨lexicalIndex, lexicalFound, lexicalStored⟩ := lexicalIH
    obtain ⟨position, selected, stored⟩ := closed.view callerStored lexicalStored generated
    exact ⟨position, by simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerFound, lexicalFound, selected], stored⟩

theorem lookup_complete {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (closed : Closed inputs table) {frame : Frame} {state : Option State}
    (authenticated : Authenticates inputs frame state) : table.lookup? frame = some state := by
  have indexed := lookupIndex_complete closed authenticated
  cases state with
  | none =>
    change table.lookupIndex? frame = some none at indexed
    simp [SourceCoreCallableAncestryPairedCache.Table.lookup?, indexed]
  | some state =>
    obtain ⟨position, selected, stored⟩ := indexed
    simp [SourceCoreCallableAncestryPairedCache.Table.lookup?, selected, stored]

theorem lookup_sound {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : Sound inputs table) {frame : Frame} {state : Option State}
    (found : table.lookup? frame = some state) : Authenticates inputs frame state := by
  cases indexed : table.lookupIndex? frame with
  | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookup?, indexed] at found
  | some result =>
    have meaning := lookupIndex_sound sound frame indexed
    cases result with
    | none =>
      simp only [SourceCoreCallableAncestryPairedCache.Table.lookup?, indexed, Option.some.injEq] at found
      subst state
      exact meaning
    | some position =>
      obtain ⟨selected, stored, ancestry⟩ := meaning
      simp only [SourceCoreCallableAncestryPairedCache.Table.lookup?, indexed, stored, Option.map_some, Option.some.injEq] at found
      subst state
      exact ancestry

theorem lookup_iff {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : Sound inputs table) (closed : Closed inputs table) {frame : Frame} {state : Option State} :
    table.lookup? frame = some state ↔ Authenticates inputs frame state :=
  ⟨lookup_sound sound, lookup_complete closed⟩

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedLookup
