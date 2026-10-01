import Solcore.SourceSemantics.Dynamic.Default
import Solcore.SourceSemantics.Dynamic.RuntimeType
import Solcore.SourceSemantics.Dynamic.Primitive
import Solcore.SourceSemantics.Places

/-!
Declarative dynamics for mutable source places.

Place resolution has three visibly separate phases.  Index expressions are
evaluated once from left to right, the selected leaf is read from the root at
the end of that phase, and a later write reconstructs the path from the latest
root cell.  Consequently effects of the right-hand side on unrelated parts of
the root survive an assignment, while compound operations can still use the
leaf snapshot captured before the right-hand side.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

/-- A place projection after all index occurrences have been evaluated. -/
inductive EvaluatedProjection where
  | index (key : Value)
  | member (name : String) (index : Nat)
  deriving Repr

/-- Abstract interface property needed to show that projection evaluation is
deterministic. -/
def ExpressionEvaluationFunctional
    (EvaluateExpression :
      Environment → Heap → ExpressionId → Value → Heap → Prop) : Prop :=
  ∀ environment before expression leftValue leftHeap rightValue rightHeap,
    EvaluateExpression environment before expression leftValue leftHeap →
    EvaluateExpression environment before expression rightValue rightHeap →
    leftValue = rightValue ∧ leftHeap = rightHeap

/-- Evaluate index occurrences exactly once from left to right.  Member
projections are pure and preserve the current heap. -/
inductive ProjectionsEvaluate
    (EvaluateExpression :
      Environment → Heap → ExpressionId → Value → Heap → Prop)
    (environment : Environment) :
    Heap → List PlaceProjection → List EvaluatedProjection → Heap → Prop where
  | nil {heap} : ProjectionsEvaluate EvaluateExpression environment heap [] [] heap
  | member
      {before after name index projections evaluated}
      (tail : ProjectionsEvaluate EvaluateExpression environment before
        projections evaluated after) :
      ProjectionsEvaluate EvaluateExpression environment before
        (.member name index :: projections)
        (.member name index :: evaluated) after
  | index
      {before middle after expression key projections evaluated}
      (head : EvaluateExpression environment before expression key middle)
      (tail : ProjectionsEvaluate EvaluateExpression environment middle
        projections evaluated after) :
      ProjectionsEvaluate EvaluateExpression environment before
        (.index expression :: projections) (.index key :: evaluated) after

namespace ProjectionsEvaluate

/-- A deterministic expression relation induces deterministic left-to-right
projection evaluation. -/
theorem functional
    {EvaluateExpression :
      Environment → Heap → ExpressionId → Value → Heap → Prop}
    (expression_functional : ExpressionEvaluationFunctional EvaluateExpression)
    {environment : Environment} {before : Heap}
    {projections : List PlaceProjection}
    {leftProjections rightProjections : List EvaluatedProjection}
    {leftHeap rightHeap : Heap}
    (left : ProjectionsEvaluate EvaluateExpression environment before projections
      leftProjections leftHeap)
    (right : ProjectionsEvaluate EvaluateExpression environment before projections
      rightProjections rightHeap) :
    leftProjections = rightProjections ∧ leftHeap = rightHeap := by
  induction left generalizing rightProjections rightHeap with
  | nil =>
      cases right
      exact ⟨rfl, rfl⟩
  | member leftTail inductionHypothesis =>
      cases right with
      | member rightTail =>
          rcases inductionHypothesis rightTail with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
  | index leftHead leftTail inductionHypothesis =>
      cases right with
      | index rightHead rightTail =>
          rcases expression_functional _ _ _ _ _ _ _ leftHead rightHead with
            ⟨rfl, rfl⟩
          rcases inductionHypothesis rightTail with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩

end ProjectionsEvaluate

/-- Structural selection from a constructor payload. -/
inductive ValueAt : List Value → Nat → Value → Prop where
  | head {value rest} : ValueAt (value :: rest) 0 value
  | tail {value rest index selected}
      (selectedAt : ValueAt rest index selected) :
      ValueAt (value :: rest) (index + 1) selected

/-- Structural replacement in a constructor payload. -/
inductive ValuesReplaceAt :
    List Value → Nat → Value → List Value → Prop where
  | head {previous rest replacement} :
      ValuesReplaceAt (previous :: rest) 0 replacement (replacement :: rest)
  | tail {previous rest index replacement updated}
      (tailReplacement : ValuesReplaceAt rest index replacement updated) :
      ValuesReplaceAt (previous :: rest) (index + 1) replacement
        (previous :: updated)

namespace ValueAt

theorem functional {values : List Value} {index : Nat} {left right : Value}
    (leftAt : ValueAt values index left) (rightAt : ValueAt values index right) :
    left = right := by
  induction leftAt with
  | head => cases rightAt; rfl
  | tail _ inductionHypothesis =>
      cases rightAt with
      | tail rightTail => exact inductionHypothesis rightTail

end ValueAt

namespace ValuesReplaceAt

theorem functional
    {values : List Value} {index : Nat} {replacement : Value}
    {left right : List Value}
    (leftReplacement : ValuesReplaceAt values index replacement left)
    (rightReplacement : ValuesReplaceAt values index replacement right) :
    left = right := by
  induction leftReplacement generalizing right with
  | head => cases rightReplacement; rfl
  | tail _ inductionHypothesis =>
      cases rightReplacement with
      | tail rightTail => rw [inductionHypothesis rightTail]

theorem length_eq
    {values updated : List Value} {index : Nat} {replacement : Value}
    (replacementAt : ValuesReplaceAt values index replacement updated) :
    updated.length = values.length := by
  induction replacementAt with
  | head => rfl
  | tail _ inductionHypothesis => simp [inductionHypothesis]

theorem selects_replacement
    {values updated : List Value} {index : Nat} {replacement : Value}
    (replacementAt : ValuesReplaceAt values index replacement updated) :
    ValueAt updated index replacement := by
  induction replacementAt with
  | head => exact .head
  | tail _ inductionHypothesis => exact .tail inductionHypothesis

end ValuesReplaceAt

/-- Runtime treatment of an uninitialized root.  Only a mapping cell is
materialized as an empty mapping; all other uninitialized cells remain absent. -/
inductive RootInitialValue : Cell → Option Value → Prop where
  | initialized {type value} :
      RootInitialValue { type := type, value := some value } (some value)
  | emptyMapping (keyType valueType : Ty) :
      RootInitialValue
        { type := .mapping keyType valueType, value := none }
        (some (.mapping keyType valueType []))
  | uninitialized
      {type : Ty}
      (not_mapping : ¬ ∃ keyType valueType, type = .mapping keyType valueType) :
      RootInitialValue { type := type, value := none } none

namespace RootInitialValue

theorem functional {cell : Cell} {left right : Option Value}
    (leftInitial : RootInitialValue cell left)
    (rightInitial : RootInitialValue cell right) : left = right := by
  cases leftInitial <;> cases rightInitial <;> simp_all

end RootInitialValue

/-- Read through an evaluated projection path.  A missing mapping entry uses
the canonical default of the mapping value type; a non-defaultable missing
entry has no derivation. -/
inductive ProjectionsRead :
    Option Value → List EvaluatedProjection → Option Value → Prop where
  | nil {current} : ProjectionsRead current [] current
  | indexFound
      {key keyType valueType entries selected projections result}
      (lookup : MappingLookup key entries selected)
      (tail : ProjectionsRead (some selected) projections result) :
      ProjectionsRead (some (.mapping keyType valueType entries))
        (.index key :: projections) result
  | indexDefault
      {key keyType valueType entries defaultValue projections result}
      (absent : MappingAbsent key entries)
      (defaulted : DefaultValue valueType defaultValue)
      (tail : ProjectionsRead (some defaultValue) projections result) :
      ProjectionsRead (some (.mapping keyType valueType entries))
        (.index key :: projections) result
  | member
      {instantiation arguments name index selected projections result}
      (selectedAt : ValueAt arguments index selected)
      (tail : ProjectionsRead (some selected) projections result) :
      ProjectionsRead (some (.constructed instantiation arguments))
        (.member name index :: projections) result

namespace ProjectionsRead

/-- Reading a fixed evaluated path is deterministic. -/
theorem functional
    {current : Option Value} {projections : List EvaluatedProjection}
    {left right : Option Value}
    (leftRead : ProjectionsRead current projections left)
    (rightRead : ProjectionsRead current projections right) : left = right := by
  induction leftRead generalizing right with
  | nil => cases rightRead; rfl
  | indexFound leftLookup _ inductionHypothesis =>
      cases rightRead with
      | indexFound rightLookup rightTail =>
          have selected_eq := leftLookup.functional rightLookup
          cases selected_eq
          exact inductionHypothesis rightTail
      | indexDefault absent _ _ =>
          exact (absent.excludes_lookup leftLookup).elim
  | indexDefault leftAbsent leftDefault _ inductionHypothesis =>
      cases rightRead with
      | indexFound rightLookup _ =>
          exact (leftAbsent.excludes_lookup rightLookup).elim
      | indexDefault _ rightDefault rightTail =>
          have default_eq := leftDefault.functional rightDefault
          cases default_eq
          exact inductionHypothesis rightTail
  | member leftAt _ inductionHypothesis =>
      cases rightRead with
      | member rightAt rightTail =>
          have selected_eq := leftAt.functional rightAt
          cases selected_eq
          exact inductionHypothesis rightTail

end ProjectionsRead

/-- A missing mapping default encountered while traversing a fixed path.
Each earlier index has passed its key-type guard and selected a real or default
value. The relation is pure: index expressions have already run, and no leaf
modifier or heap write has occurred. Other projection failures are not covered. -/
inductive ProjectionsFaults :
    Option Value → List EvaluatedProjection → SemanticFault → Prop where
  | indexDefaultUnavailable
      {key keyType valueType entries projections}
      (key_type : ValueRuntimeTypeMatches key keyType)
      (absent : MappingAbsent key entries)
      (not_defaultable : ¬ Defaultable valueType) :
      ProjectionsFaults (some (.mapping keyType valueType entries))
        (.index key :: projections) (.missingMappingDefault valueType)
  | indexFound
      {key keyType valueType entries selected projections reason}
      (key_type : ValueRuntimeTypeMatches key keyType)
      (lookup : MappingLookup key entries selected)
      (tail : ProjectionsFaults (some selected) projections reason) :
      ProjectionsFaults (some (.mapping keyType valueType entries))
        (.index key :: projections) reason
  | indexDefault
      {key keyType valueType entries defaultValue projections reason}
      (key_type : ValueRuntimeTypeMatches key keyType)
      (absent : MappingAbsent key entries)
      (defaulted : DefaultValue valueType defaultValue)
      (tail : ProjectionsFaults (some defaultValue) projections reason) :
      ProjectionsFaults (some (.mapping keyType valueType entries))
        (.index key :: projections) reason
  | member
      {instantiation arguments name index selected projections reason}
      (selectedAt : ValueAt arguments index selected)
      (tail : ProjectionsFaults (some selected) projections reason) :
      ProjectionsFaults (some (.constructed instantiation arguments))
        (.member name index :: projections) reason

namespace ProjectionsFaults

/-- A structural missing-default failure cannot also select a leaf. -/
theorem excludes_read
    {current : Option Value} {projections : List EvaluatedProjection}
    {reason : SemanticFault} (fault : ProjectionsFaults current projections reason)
    {selected : Option Value} : ¬ ProjectionsRead current projections selected := by
  induction fault generalizing selected with
  | indexDefaultUnavailable _ absent notDefaultable =>
      intro selectedRead
      cases selectedRead with
      | indexFound lookup _ => exact absent.excludes_lookup lookup
      | indexDefault _ defaulted _ => exact notDefaultable defaulted.defaultable
  | indexFound _ lookup _ inductionHypothesis =>
      intro selectedRead
      cases selectedRead with
      | indexFound otherLookup tail =>
          have equal := lookup.functional otherLookup
          cases equal
          exact inductionHypothesis tail
      | indexDefault absent _ _ => exact absent.excludes_lookup lookup
  | indexDefault _ absent defaulted _ inductionHypothesis =>
      intro selectedRead
      cases selectedRead with
      | indexFound lookup _ => exact absent.excludes_lookup lookup
      | indexDefault _ otherDefault tail =>
          have equal := defaulted.functional otherDefault
          cases equal
          exact inductionHypothesis tail
  | member selectedAt _ inductionHypothesis =>
      intro selectedRead
      cases selectedRead with
      | member otherAt tail =>
          have equal := selectedAt.functional otherAt
          cases equal
          exact inductionHypothesis tail

end ProjectionsFaults

/-- A leaf modification relation is deterministic when it chooses at most one
replacement for each current optional value. -/
def LeafModificationFunctional
    (Modify : Option Value → Value → Prop) : Prop :=
  ∀ current left right, Modify current left → Modify current right → left = right

/-- Rebuild an evaluated place path after modifying its selected leaf.
Mapping writes replace the first equivalent key or append when absent;
constructor writes preserve the constructor instantiation and every other
payload position. -/
inductive ProjectionsUpdate (Modify : Option Value → Value → Prop) :
    Option Value → List EvaluatedProjection → Value → Prop where
  | leaf
      {current updated}
      (modified : Modify current updated) :
      ProjectionsUpdate Modify current [] updated
  | indexFound
      {key keyType valueType entries selected projections updatedChild
        updatedEntries}
      (lookup : MappingLookup key entries selected)
      (child : ProjectionsUpdate Modify (some selected) projections updatedChild)
      (insert : MappingInsert key updatedChild entries updatedEntries) :
      ProjectionsUpdate Modify (some (.mapping keyType valueType entries))
        (.index key :: projections)
        (.mapping keyType valueType updatedEntries)
  | indexDefault
      {key keyType valueType entries defaultValue projections updatedChild
        updatedEntries}
      (absent : MappingAbsent key entries)
      (defaulted : DefaultValue valueType defaultValue)
      (child : ProjectionsUpdate Modify (some defaultValue) projections updatedChild)
      (insert : MappingInsert key updatedChild entries updatedEntries) :
      ProjectionsUpdate Modify (some (.mapping keyType valueType entries))
        (.index key :: projections)
        (.mapping keyType valueType updatedEntries)
  | member
      {instantiation arguments name index selected projections updatedChild
        updatedArguments}
      (selectedAt : ValueAt arguments index selected)
      (child : ProjectionsUpdate Modify (some selected) projections updatedChild)
      (replace : ValuesReplaceAt arguments index updatedChild updatedArguments) :
      ProjectionsUpdate Modify (some (.constructed instantiation arguments))
        (.member name index :: projections)
        (.constructed instantiation updatedArguments)

namespace ProjectionsUpdate

/-- Successful reconstruction must have reached a readable leaf through the
same structural path, independently of the leaf modification relation. -/
theorem readable
    {Modify : Option Value → Value → Prop}
    {current : Option Value} {projections : List EvaluatedProjection}
    {updated : Value} (update : ProjectionsUpdate Modify current projections updated) :
    ∃ selected, ProjectionsRead current projections selected := by
  induction update with
  | leaf => exact ⟨_, .nil⟩
  | indexFound lookup _ _ inductionHypothesis =>
      obtain ⟨selected, read⟩ := inductionHypothesis
      exact ⟨selected, .indexFound lookup read⟩
  | indexDefault absent defaulted _ _ inductionHypothesis =>
      obtain ⟨selected, read⟩ := inductionHypothesis
      exact ⟨selected, .indexDefault absent defaulted read⟩
  | member selectedAt _ _ inductionHypothesis =>
      obtain ⟨selected, read⟩ := inductionHypothesis
      exact ⟨selected, .member selectedAt read⟩

/-- A deterministic leaf operation induces a deterministic structural update. -/
theorem functional
    {Modify : Option Value → Value → Prop}
    (modify_functional : LeafModificationFunctional Modify)
    {current : Option Value} {projections : List EvaluatedProjection}
    {left right : Value}
    (leftUpdate : ProjectionsUpdate Modify current projections left)
    (rightUpdate : ProjectionsUpdate Modify current projections right) :
    left = right := by
  induction leftUpdate generalizing right with
  | leaf leftModified =>
      cases rightUpdate with
      | leaf rightModified => exact modify_functional _ _ _ leftModified rightModified
  | indexFound leftLookup _ leftInsert inductionHypothesis =>
      cases rightUpdate with
      | indexFound rightLookup rightChild rightInsert =>
          have selected_eq := leftLookup.functional rightLookup
          cases selected_eq
          have child_eq := inductionHypothesis rightChild
          cases child_eq
          rw [leftInsert.functional rightInsert]
      | indexDefault absent _ _ _ =>
          exact (absent.excludes_lookup leftLookup).elim
  | indexDefault leftAbsent leftDefault _ leftInsert inductionHypothesis =>
      cases rightUpdate with
      | indexFound rightLookup _ _ =>
          exact (leftAbsent.excludes_lookup rightLookup).elim
      | indexDefault _ rightDefault rightChild rightInsert =>
          have default_eq := leftDefault.functional rightDefault
          cases default_eq
          have child_eq := inductionHypothesis rightChild
          cases child_eq
          rw [leftInsert.functional rightInsert]
  | member leftAt _ leftReplace inductionHypothesis =>
      cases rightUpdate with
      | member rightAt rightChild rightReplace =>
          have selected_eq := leftAt.functional rightAt
          cases selected_eq
          have child_eq := inductionHypothesis rightChild
          cases child_eq
          rw [leftReplace.functional rightReplace]

end ProjectionsUpdate

theorem ProjectionsFaults.excludes_update
    {Modify : Option Value → Value → Prop}
    {current : Option Value} {projections : List EvaluatedProjection}
    {reason : SemanticFault} (fault : ProjectionsFaults current projections reason)
    {updated : Value} : ¬ ProjectionsUpdate Modify current projections updated := by
  intro update
  obtain ⟨selected, read⟩ := update.readable
  exact fault.excludes_read read

/-- A resolved semantic place.  `selected` is the leaf snapshot captured
after target-index evaluation and before a right-hand side is evaluated. -/
structure ResolvedPlace where
  location : Location
  rootType : Ty
  valueType : Ty
  projections : List EvaluatedProjection
  selected : Option Value
  deriving Repr

/-- Resolve a retained place.  The first read establishes that its location is
live before index effects; the second read deliberately observes the root
after those effects. -/
inductive PlaceResolves
    (EvaluateExpression :
      Environment → Heap → ExpressionId → Value → Heap → Prop)
    (environment : Environment) :
    Heap → PlaceResolution → ResolvedPlace → Heap → Prop where
  | intro
      {before after : Heap} {place : PlaceResolution}
      {location : Location} {initialCell currentCell : Cell}
      {evaluated : List EvaluatedProjection}
      {initial selected : Option Value}
      (root_lookup : Environment.LooksUp environment place.root location)
      (initial_read : Heap.Reads before location initialCell)
      (evaluate : ProjectionsEvaluate EvaluateExpression environment before
        place.projections evaluated after)
      (current_read : Heap.Reads after location currentCell)
      (initial_value : RootInitialValue currentCell initial)
      (selection : ProjectionsRead initial evaluated selected) :
      PlaceResolves EvaluateExpression environment before place
        { location := location
          rootType := currentCell.type
          valueType := place.type
          projections := evaluated
          selected := selected }
        after

namespace PlaceResolves

/-- With deterministic expression evaluation, resolving a fixed place fixes
both the captured target and the post-index heap. -/
theorem functional
    {EvaluateExpression :
      Environment → Heap → ExpressionId → Value → Heap → Prop}
    (expression_functional : ExpressionEvaluationFunctional EvaluateExpression)
    {environment : Environment} {before : Heap} {place : PlaceResolution}
    {leftTarget rightTarget : ResolvedPlace} {leftHeap rightHeap : Heap}
    (left : PlaceResolves EvaluateExpression environment before place leftTarget
      leftHeap)
    (right : PlaceResolves EvaluateExpression environment before place rightTarget
      rightHeap) :
    leftTarget = rightTarget ∧ leftHeap = rightHeap := by
  cases left with
  | intro leftLookup leftInitialRead leftEvaluate leftCurrentRead
      leftInitialValue leftSelection =>
      cases right with
      | intro rightLookup rightInitialRead rightEvaluate rightCurrentRead
          rightInitialValue rightSelection =>
          have location_eq := leftLookup.functional rightLookup
          cases location_eq
          have initial_cell_eq := leftInitialRead.functional rightInitialRead
          cases initial_cell_eq
          rcases leftEvaluate.functional expression_functional rightEvaluate with
            ⟨evaluated_eq, heap_eq⟩
          cases evaluated_eq
          cases heap_eq
          have current_cell_eq := leftCurrentRead.functional rightCurrentRead
          cases current_cell_eq
          have initial_eq := leftInitialValue.functional rightInitialValue
          cases initial_eq
          have selected_eq := leftSelection.functional rightSelection
          cases selected_eq
          exact ⟨rfl, rfl⟩

end PlaceResolves

/-- Write a resolved place into the latest heap.  The current root cell, not
the root captured during resolution, supplies all structure outside the
selected leaf.  Its retained type must still equal the captured root type. -/
inductive ResolvedPlaceWrites (Modify : Option Value → Value → Prop) :
    Heap → ResolvedPlace → Value → Heap → Prop where
  | intro
      {before after : Heap} {place : ResolvedPlace}
      {currentCell : Cell} {initial : Option Value} {updatedRoot : Value}
      (current_read : Heap.Reads before place.location currentCell)
      (root_type_eq : currentCell.type = place.rootType)
      (initial_value : RootInitialValue currentCell initial)
      (update : ProjectionsUpdate Modify initial place.projections updatedRoot)
      (write : Heap.Writes before place.location (some updatedRoot) after) :
      ResolvedPlaceWrites Modify before place updatedRoot after

/-- Plain assignment ignores the previous leaf and installs the evaluated
right-hand value. -/
inductive ReplacesWith (replacement : Value) : Option Value → Value → Prop where
  | intro (current : Option Value) : ReplacesWith replacement current replacement

namespace ReplacesWith

theorem functional (replacement : Value) :
    LeafModificationFunctional (ReplacesWith replacement) := by
  intro current left right leftReplacement rightReplacement
  cases leftReplacement
  cases rightReplacement
  rfl

end ReplacesWith

/-- A complete assignment transaction.  Target resolution (and therefore the
snapshot) precedes right-hand evaluation.  The final write starts from the
heap produced by the right-hand side and supplies the old snapshot explicitly
to the compound leaf operation. -/
inductive PlaceAssignment
    (EvaluateExpression :
      Environment → Heap → ExpressionId → Value → Heap → Prop)
    (Combine : Option Value → Value → Value → Prop)
    (environment : Environment) :
    Heap → PlaceResolution → ExpressionId → Value → Heap → Prop where
  | intro
      {before targetHeap rhsHeap after : Heap}
      {place : PlaceResolution} {target : ResolvedPlace}
      {rightExpression : ExpressionId} {rightValue updatedRoot : Value}
      (resolve : PlaceResolves EvaluateExpression environment before place target
        targetHeap)
      (evaluate_right : EvaluateExpression environment targetHeap rightExpression
        rightValue rhsHeap)
      (write : ResolvedPlaceWrites
        (fun _ updated => Combine target.selected rightValue updated)
        rhsHeap target updatedRoot after) :
      PlaceAssignment EvaluateExpression Combine environment before place
        rightExpression updatedRoot after

/-- A snapshot-based update without a right-hand expression, used by unary
assignment forms. -/
inductive PlaceSnapshotUpdate
    (EvaluateExpression :
      Environment → Heap → ExpressionId → Value → Heap → Prop)
    (ModifySnapshot : Option Value → Value → Prop)
    (environment : Environment) :
    Heap → PlaceResolution → Value → Heap → Prop where
  | intro
      {before selectedHeap after : Heap}
      {place : PlaceResolution} {target : ResolvedPlace} {updatedRoot : Value}
      (resolve : PlaceResolves EvaluateExpression environment before place target
        selectedHeap)
      (write : ResolvedPlaceWrites
        (fun _ updated => ModifySnapshot target.selected updated)
        selectedHeap target updatedRoot after) :
      PlaceSnapshotUpdate EvaluateExpression ModifySnapshot environment before
        place updatedRoot after

namespace ResolvedPlaceWrites

/-- Every successful place write is a type-preserving heap-world extension at
the level of retained cell annotations. -/
theorem types_extend
    {Modify : Option Value → Value → Prop}
    {before after : Heap} {place : ResolvedPlace} {updatedRoot : Value}
    (written : ResolvedPlaceWrites Modify before place updatedRoot after) :
    HeapTypesExtend before after := by
  cases written with
  | intro _ _ _ _ write => exact HeapTypesExtend.of_write write

end ResolvedPlaceWrites

end Solcore.SourceSemantics.Dynamic
