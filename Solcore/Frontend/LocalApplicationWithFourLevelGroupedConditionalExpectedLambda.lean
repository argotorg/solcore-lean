import Solcore.Frontend.FourLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithThreeLevelGroupedConditionalExpectedLambda

/-!
Selects the exact ADR-0332 four-level grouped conditional application before
the complete unchanged ADR-0331 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0332 child or the
complete unchanged ADR-0331 child. -/
inductive LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | fourLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0332 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized four-level grouped conditional invokes exactly ADR-0332. -/
theorem elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0331 result. -/
theorem elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for four-level-first dispatch. -/
theorem elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .fourLevelGroupedConditional boundary
        (elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | fourLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | fourLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | fourLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend
