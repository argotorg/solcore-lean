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

/-- Over the wider profile, the native modifier gives a leaf. The operands are represented at `leaf`,
whose view is the target's; the profile, the compiler's modifier and the source's relation are at the
target's type. The source's result, whenever it applies the operation, is that leaf, represented at
`leaf`; when it panics, no result is asked to be represented, since a fixed-width leaf of a
panicking checked operation need not be canonical. The check after the setter agrees with the
source. -/
theorem wide_outcome
    (observations : FunctionObservations checked.catalog functions identities)
    {targetType leaf : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : WideAssignmentProfile operator targetType)
    (leafView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType targetType)
    (leftRep : ValueRep checked registry functions mapping world leaf left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world leaf right rightCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value,
      Evaluates environment store
        (modified type (assignmentModifier targetType (type = .integer) operator) false snapshot rhs invalid
          (SourceCoreDataPlaces.placeWrap targetType operator false)) (.inRight .word value) store ∧
      RuntimeValueHasType world value type ambient.definitions ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right ∧
      (∀ other, Dynamic.CompoundAssignmentApplies targetType operator (some left) right other →
        other = result ∧ ValueRep checked registry functions mapping world leaf result value type) ∧
      ∀ {leftType : Ty}, FixedCompoundModifier.Agreement targetType operator (some left) right result
        (assignmentModifier targetType (type = .integer) operator) (.inRight leftType leftCore) rightCore := by
  rcases profile with narrow | ⟨⟨fixedType, rfl⟩, kind⟩
  · have none := checkedCompound_of_profile narrow
    have plain := DataPlaceModifier.plain_of_checkedCompound none
    have relation := Dynamic.CompoundAssignmentApplies.eq_of_plain plain
    have leafProfile : AssignmentProfile operator (SourceCoreRawMetadata.runtimeType leaf) := leafView ▸ narrow
    rw [assignmentModifier_plain none, SourceCoreDataPlaces.placeWrap_plain none, relation]
    obtain ⟨result, value, related, evaluated, outcome⟩ :=
      initialized_outcome observations leafProfile leftRep rightRep snapshotSelected rightSelected store invalid
    refine ⟨result, value, evaluated, related.runtime_hasType, ?_, ?_, ?_⟩
    · rcases outcome with ⟨_, valid⟩ | ⟨_, _, _, panics⟩
      · exact valid
      · exact DataPlaceModifier.panic_excludes_invalid (panics .word)
    · intro other applied
      rcases outcome with ⟨applies, _⟩ | ⟨_, _, _, panics⟩
      · exact ⟨DataPlaceModifier.assignment_functional applied applies, related⟩
      · exact (panic_excludes_applies plain (panics targetType) applied).elim
    · intro leftType
      rcases outcome with ⟨applies, _⟩ | ⟨operation, selected, zero, panics⟩
      · have passes := passes_of_applies observations leafProfile rightRep applies (type = .integer)
        exact .applied (.primitive plain applies) (.inl passes)
          ⟨(DataPlaceGuard.agreement passes).unwrap, (DataPlaceGuard.agreement passes).wrap⟩
      · subst zero
        refine .panicked _ (panics targetType)
          (fun other applied => panic_excludes_applies plain (panics targetType) (relation ▸ applied)) ?_
        intro binders store after outputType write value updated changed
        rw [selected]
        exact FixedCompoundModifier.guard_divisor_zero _ _
  · have view : SourceCoreRawMetadata.runtimeType leaf = .fixed fixedType := leafView
    obtain ⟨leftWord, rfl, rfl, rfl, leftCanonical⟩ := CompatibleExpressionPrimitives.fixed_fields leftRep view
    obtain ⟨rightWord, rfl, rfl, _, rightCanonical⟩ := CompatibleExpressionPrimitives.fixed_fields rightRep view
    have integer : decide (Ty.word = Ty.integer) = false := rfl
    simp only [integer]
    refine ⟨.word (FixedCompoundModifier.leaf fixedType operator leftWord rightWord),
      .word (FixedCompoundModifier.leaf fixedType operator leftWord rightWord),
      FixedCompoundModifier.compatible_modified_evaluates kind snapshotSelected rightSelected store invalid, .word,
      FixedCompoundModifier.words_valid kind leftWord rightWord, ?_, ?_⟩
    · intro other applied
      have same := FixedCompoundModifier.applies_leaf kind applied
      subst same
      obtain ⟨word, same, canonical⟩ :=
        FixedCompoundModifier.canonical_of_applies kind leftCanonical rightCanonical applied
      cases same
      exact ⟨rfl, .compatible leafView (.fixed _ canonical)⟩
    · intro leftType
      rw [FixedCompoundModifier.compatible_assignmentModifier]
      exact FixedCompoundModifier.guard_agrees kind leftWord rightWord

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
end
