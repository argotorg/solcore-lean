import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FixedModifiers
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback

/-!
# Compatible places: the wider assignment profile

The modifier of a compatible place assignment over `WideAssignmentProfile`, stated with the
compiler's actual modifier (`assignmentModifier`), its wrap (`SourceCoreDataPlaces.placeWrap`) and
the source's relation at the target's type (`Dynamic.CompoundAssignmentApplies`). The existing
profile reduces to `CompatiblePlaceModifier.initialized_outcome`; a fixed-width target takes
`FixedCompoundModifier`. The place pipelines do not use it yet.

Main declarations:
- `CompatiblePlaceModifier.wide_outcome`: the native modifier gives a leaf; whenever the source
  applies the operation its result is that leaf, represented at the target; and the check after
  the setter agrees with the source (`FixedCompoundModifier.Agreement`).
-/

section
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
open Core Frontend SourceInference GeneralHeap DataEquality CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {identities : Dynamic.Value → Word → Prop}

/-- Over the wider profile, the native modifier gives a leaf. The source's result, whenever it
applies the operation, is that leaf, represented at the target; when it panics, no result is
asked to be represented, since a fixed-width leaf of a panicking checked operation need not be
canonical. The check after the setter agrees with the source. -/
theorem wide_outcome
    (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : WideAssignmentProfile operator sourceType)
    (leftRep : ValueRep checked registry functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value,
      Evaluates environment store
        (modified type (assignmentModifier sourceType (type = .integer) operator) false snapshot rhs invalid
          (SourceCoreDataPlaces.placeWrap sourceType operator false)) (.inRight .word value) store ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right ∧
      (∀ other, Dynamic.CompoundAssignmentApplies sourceType operator (some left) right other →
        other = result ∧ ValueRep checked registry functions mapping world sourceType result value type) ∧
      ∀ {binders : Environment} {written : Store} {outputType leftType : Ty} {write : Expr}
        {updated changed : Value},
        FixedCompoundModifier.Agreement sourceType operator (some left) right result
          (updated :: changed :: rightCore :: .inRight leftType leftCore :: binders) written
          (SourceCoreDataPlaces.guard outputType (assignmentModifier sourceType (type = .integer) operator) write)
          write outputType := by
  rcases profile with narrow | ⟨⟨fixedType, rfl⟩, kind⟩
  · have none := checkedCompound_of_profile narrow
    have plain := DataPlaceModifier.plain_of_checkedCompound none
    have relation := Dynamic.CompoundAssignmentApplies.eq_of_plain plain
    rw [assignmentModifier_plain none, SourceCoreDataPlaces.placeWrap_plain none]
    obtain ⟨result, value, related, evaluated, outcome⟩ :=
      initialized_outcome observations narrow leftRep rightRep snapshotSelected rightSelected store invalid
    refine ⟨result, value, evaluated, ?_, ?_, ?_⟩
    · rcases outcome with ⟨_, valid⟩ | ⟨_, _, _, panics⟩
      · exact valid
      · exact DataPlaceModifier.panic_excludes_invalid (panics .word)
    · intro other applied
      rw [relation] at applied
      rcases outcome with ⟨applies, _⟩ | ⟨_, _, _, panics⟩
      · exact ⟨DataPlaceModifier.assignment_functional applied applies, related⟩
      · exact (panic_excludes_applies plain (panics sourceType) applied).elim
    · intro binders written outputType leftType write updated changed
      rcases outcome with ⟨applies, _⟩ | ⟨operation, selected, zero, panics⟩
      · have passes := passes_of_applies observations narrow rightRep applies (type = .integer)
        refine .applied (relation ▸ applies) fun value after => ⟨fun evaluated => ?_,
          SourceCoreDataPlaces.guard_passes passes⟩
        rcases SourceCoreDataPlaces.guard_inv evaluated with ⟨_, written⟩ | ⟨_, selected', zero', _, _⟩ |
            ⟨_, _, _, ranged, _⟩
        · exact written
        · rw [selected', zero'] at passes
          cases passes with
          | total total => cases total _ rfl
          | nonzero nonzero => exact (nonzero rfl).elim
        · exact absurd ranged binaryOperator_not_range
      · subst zero
        rw [selected]
        exact .panicked _ (panics sourceType)
          (fun other applied => panic_excludes_applies plain (panics sourceType) (relation ▸ applied))
          FixedCompoundModifier.guard_divisor_zero
  · obtain ⟨leftWord, rfl, rfl, rfl, leftCanonical⟩ := CompatibleExpressionPrimitives.fixed_fields leftRep rfl
    obtain ⟨rightWord, rfl, rfl, _, rightCanonical⟩ := CompatibleExpressionPrimitives.fixed_fields rightRep rfl
    have integer : decide (Ty.word = Ty.integer) = false := rfl
    simp only [integer]
    refine ⟨.word (FixedCompoundModifier.leaf fixedType operator leftWord rightWord),
      .word (FixedCompoundModifier.leaf fixedType operator leftWord rightWord),
      FixedCompoundModifier.compatible_modified_evaluates kind snapshotSelected rightSelected store invalid,
      FixedCompoundModifier.words_valid kind leftWord rightWord, ?_, ?_⟩
    · intro other applied
      have same := FixedCompoundModifier.applies_leaf kind applied
      subst same
      obtain ⟨word, same, canonical⟩ :=
        FixedCompoundModifier.canonical_of_applies kind leftCanonical rightCanonical applied
      cases same
      exact ⟨rfl, .fixed _ canonical⟩
    · intro binders written outputType leftType write updated changed
      rw [FixedCompoundModifier.compatible_assignmentModifier]
      exact FixedCompoundModifier.guard_agrees kind leftWord rightWord

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
end
