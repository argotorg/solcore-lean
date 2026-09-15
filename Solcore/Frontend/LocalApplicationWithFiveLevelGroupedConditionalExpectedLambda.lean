import Solcore.Frontend.FiveLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithFourLevelGroupedConditionalExpectedLambda

/-!
Selects the exact ADR-0334 five-level grouped conditional application before
the complete unchanged ADR-0333 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0334 child or the
complete unchanged ADR-0333 child. -/
inductive LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | fiveLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0334 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized five-level grouped conditional invokes exactly ADR-0334. -/
theorem elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0333 result. -/
theorem elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for five-level-first dispatch. -/
theorem elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .fiveLevelGroupedConditional boundary
        (elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | fiveLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | fiveLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | fiveLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend
