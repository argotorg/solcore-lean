import Solcore.Frontend.ConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.ThreeOrMoreGroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithTwoLevelGroupedExpectedLambda

/-!
One source-only conditional-first entry adds ADR-0324 and ADR-0323 before the
complete unchanged ADR-0322 local-application entry.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Three source-disjoint paths retain the complete selected child. -/
inductive LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | conditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (conditionalBoundary :
        isConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : ConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type
  | threeOrMoreGrouped {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (conditionalBoundary :
        isConditionalExpectedLambdaArgumentApplication source = false)
      (groupedBoundary :
        isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true)
      (elaboration : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (conditionalBoundary :
        isConditionalExpectedLambdaArgumentApplication source = false)
      (groupedBoundary :
        isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch only from the unchanged original source. Selected failure is final. -/
def elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isConditionalExpectedLambdaArgumentApplication source then
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs source
  else if isThreeOrMoreGroupedExpectedLambdaArgumentApplication source then
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs source
  else elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
    types owner inputs source

/-- A recognized conditional invokes exactly ADR-0324. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_conditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source =
      elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs source := by
  simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?, boundary]

/-- A nonconditional finite spine invokes exactly ADR-0323. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_threeOrMoreGrouped
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (conditionalBoundary :
      isConditionalExpectedLambdaArgumentApplication source = false)
    (groupedBoundary :
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source =
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?,
    conditionalBoundary, groupedBoundary]

/-- Every doubly unrecognized source has exactly the frozen ADR-0322 result. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (conditionalBoundary :
      isConditionalExpectedLambdaArgumentApplication source = false)
    (groupedBoundary :
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?,
    conditionalBoundary, groupedBoundary]

/-- Exact executable/declarative correspondence for conditional-first dispatch. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? at accepted
    split at accepted
    · rename_i conditionalBoundary
      exact .conditional conditionalBoundary
        (elaborateConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i conditionalNot
      have conditionalBoundary :
          isConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality : isConditionalExpectedLambdaArgumentApplication source <;> simp_all
      split at accepted
      · rename_i groupedBoundary
        exact .threeOrMoreGrouped conditionalBoundary groupedBoundary
          (elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mp accepted)
      · rename_i groupedNot
        have groupedBoundary :
            isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false := by
          cases equality :
              isThreeOrMoreGroupedExpectedLambdaArgumentApplication source <;> simp_all
        exact .existing conditionalBoundary groupedBoundary
          (elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | conditional boundary child =>
        simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?, boundary,
          elaborateConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | threeOrMoreGrouped conditionalBoundary groupedBoundary child =>
        simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?,
          conditionalBoundary, groupedBoundary,
          elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing conditionalBoundary groupedBoundary child =>
        simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?,
          conditionalBoundary, groupedBoundary,
          elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source path. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted :
        elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
          types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mp
          accepted⟩)

/-- Every selected child preserves its exact inferred Core type. -/
theorem LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | conditional _ child => exact child.core_hasType
  | threeOrMoreGrouped _ _ child => exact child.core_hasType
  | existing _ _ child => exact child.core_hasType

/-- Inversion exposes the ordered source partition and complete selected child. -/
theorem LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
    (isConditionalExpectedLambdaArgumentApplication source = true ∧
      ConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isConditionalExpectedLambdaArgumentApplication source = false ∧
      ((isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true ∧
        ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
          types owner inputs source core type) ∨
       (isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false ∧
        LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
          types owner inputs source core type))) := by
  cases elaboration with
  | conditional boundary child => exact .inl ⟨boundary, child⟩
  | threeOrMoreGrouped conditionalBoundary groupedBoundary child =>
      exact .inr ⟨conditionalBoundary, .inl ⟨groupedBoundary, child⟩⟩
  | existing conditionalBoundary groupedBoundary child =>
      exact .inr ⟨conditionalBoundary, .inr ⟨groupedBoundary, child⟩⟩

end Solcore.Frontend
