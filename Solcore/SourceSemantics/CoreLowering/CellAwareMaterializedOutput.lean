import Solcore.SourceSemantics.CoreLowering.CellAwareScopeGeneralizedReadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections

/-! Positive materialized provenance survives products, actual output selection
and later heap growth. A public handle never supplies this provenance alone. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open GeneralizedLocalMaterializedAssociation
open RecursiveNamedPublicFunctionHistory (Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

inductive ValueAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (location : Core.Location) :
    Dynamic.Value → Core.Value → Prop where
  | function {function native bindings parameter result}
      (association : Association compiled mapping world function native bindings parameter result)
      (framed : association.AtFrame location) :
      ValueAt compiled mapping world location (.closure function) native
  | product {left right first second}
      (leftValue : ValueAt compiled mapping world location left first)
      (rightValue : ValueAt compiled mapping world location right second) :
      ValueAt compiled mapping world location (.product left right) (.pair first second)

variable {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {location : Core.Location}
  {source : Dynamic.Value} {native : Core.Value}

theorem ValueAt.extend (value : ValueAt compiled mapping world location source native)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    ValueAt compiled nextMap nextWorld location source native := by
  induction value with
  | function association framed =>
      exact .function (association.extend maps worlds) (by cases association; exact framed)
  | product left right ihLeft ihRight => exact .product ihLeft ihRight

theorem of_read {outcome : Staging.Recursive.Outcome} {value : Core.Value}
    (strong : CellAwareScopeGeneralizedReadBounds.StrongResult (compiled := compiled)
      mapping world location outcome value) (success : outcome = .value source) :
    ∃ payload, value = .inRight .word payload ∧ ValueAt compiled mapping world location source payload := by
  obtain ⟨function, payload, bindings, parameter, result, sourceEq, valueEq, association, framed⟩ := strong source success
  exact ⟨payload, valueEq, sourceEq ▸ .function association framed⟩

theorem ValueAt.callable (value : ValueAt compiled mapping world location source native)
    {context : SourceSemantics.Context} {heap : Dynamic.Heap} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap source (.function parameter result)) :
    ∃ function bindings parameterCore resultCore, source = .closure function ∧
      ∃ association : Association compiled mapping world function native bindings parameterCore resultCore,
        association.AtFrame location := by
  cases value with
  | function association framed => exact ⟨_, _, _, _, rfl, association, framed⟩
  | product left right => cases typed

/-- The complete selected list retains the exact Source/native leaf pairing. -/
def EntriesAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (location : Core.Location) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, ValueAt compiled mapping world location entry.source entry.native

theorem selected {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value}
    {selection : RecursiveNamedPublicOutputSelections.Selection sourceType publicValue}
    {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (receipt : RecursiveNamedPublicOutputSelections.Selected selection source native type fuel entries)
    (value : ValueAt compiled mapping world location source native) :
    EntriesAt compiled mapping world location entries := by
  induction receipt with
  | skip => intro entry member; cases member
  | function =>
      intro entry member
      cases List.mem_singleton.mp member
      exact value
  | product left right ihLeft ihRight =>
      cases value with
      | product first second =>
          intro entry member
          rcases List.mem_append.mp member with inLeft | inRight
          · exact ihLeft first entry inLeft
          · exact ihRight second entry inRight

theorem EntriesAt.extend {entries : List Entry}
    (entriesAt : EntriesAt compiled mapping world location entries)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    EntriesAt compiled nextMap nextWorld location entries :=
  fun entry member => (entriesAt entry member).extend maps worlds

theorem EntriesAt.append {first second : List Entry}
    (left : EntriesAt compiled mapping world location first)
    (right : EntriesAt compiled mapping world location second) :
    EntriesAt compiled mapping world location (first ++ second) := by
  intro entry member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact left entry inLeft
  · exact right entry inRight

/-- Success retains positive function leaves; failures carry no output leaf. -/
def OutcomeAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (location : Core.Location)
    (outcome : Staging.Recursive.Outcome) (native : Core.Value) : Prop :=
  ∀ source, outcome = .value source →
    ∃ payload, native = .inRight .word payload ∧ ValueAt compiled mapping world location source payload

theorem OutcomeAt.fault {failure : Staging.Recursive.Failure} {native : Core.Value} :
    OutcomeAt compiled mapping world location (.fault failure) native := by
  intro source impossible
  cases impossible

theorem OutcomeAt.extend {outcome : Staging.Recursive.Outcome}
    (output : OutcomeAt compiled mapping world location outcome native)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    OutcomeAt compiled nextMap nextWorld location outcome native := by
  intro source same
  obtain ⟨payload, nativeEq, value⟩ := output source same
  exact ⟨payload, nativeEq, value.extend maps worlds⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedOutput
