import Solcore.Frontend.ThreeLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithTwoLevelGroupedConditionalExpectedLambda

/-!
Selects the exact ADR-0330 three-level grouped conditional application before
the complete unchanged ADR-0329 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0330 child or the
complete unchanged ADR-0329 child. -/
inductive LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | threeLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0330 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized three-level grouped conditional invokes exactly ADR-0330. -/
theorem elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0329 result. -/
theorem elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for three-level-first dispatch. -/
theorem elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .threeLevelGroupedConditional boundary
        (elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | threeLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | threeLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | threeLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend
