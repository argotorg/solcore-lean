import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedOutput

/-! Each retained exported function keeps its own immutable owner and actual
materialized compiler association. Different factories may share one history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedRetainedEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Key OwnedKey)
open RecursiveNamedPublicFunctionHistory (Entry)
open GeneralizedLocalMaterializedAssociation
open CellAwareMaterializedOutput (ValueAt EntriesAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}

def EntryAt (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (mapping : LocationMap) (world : StoreTyping) (entry : Entry) : Prop :=
  ∃ owner : OwnedKey keys,
    ValueAt compiled mapping world owner.key.frameLocation entry.source entry.native

def Retained (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (mapping : LocationMap) (world : StoreTyping) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, EntryAt keys mapping world entry

theorem EntryAt.extend {entry : Entry} (retained : EntryAt keys mapping world entry)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    EntryAt keys nextMap nextWorld entry := by
  obtain ⟨owner, value⟩ := retained
  exact ⟨owner, value.extend maps worlds⟩

theorem Retained.extend {entries : List Entry} (retained : Retained keys mapping world entries)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    Retained keys nextMap nextWorld entries :=
  fun entry member => (retained entry member).extend maps worlds

theorem Retained.nil : Retained keys mapping world [] := by
  intro entry member
  cases member

theorem Retained.of_selected {entries : List Entry} (owner : OwnedKey keys)
    (selected : EntriesAt compiled mapping world owner.key.frameLocation entries) :
    Retained keys mapping world entries :=
  fun entry member => ⟨owner, selected entry member⟩

theorem Retained.append {first second : List Entry}
    (left : Retained keys mapping world first) (right : Retained keys mapping world second) :
    Retained keys mapping world (first ++ second) := by
  intro entry member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact left entry inLeft
  · exact right entry inRight

theorem EntryAt.association {entry : Entry} (retained : EntryAt keys mapping world entry)
    {function : Dynamic.Closure} (sourceEq : entry.source = .closure function) :
    ∃ (owner : OwnedKey keys), ∃ bindings parameter result,
      ∃ association : Association compiled mapping world function entry.native bindings parameter result,
        association.AtFrame owner.key.frameLocation := by
  obtain ⟨owner, value⟩ := retained
  rw [sourceEq] at value
  cases value with
  | function association framed => exact ⟨owner, _, _, _, association, framed⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedRetainedEntries
