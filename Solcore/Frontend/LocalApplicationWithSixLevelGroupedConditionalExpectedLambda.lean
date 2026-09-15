import Solcore.Frontend.SixLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithFiveLevelGroupedConditionalExpectedLambda

/-!
Selects the exact ADR-0336 six-level grouped conditional application before
the complete unchanged ADR-0335 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0336 child or the
complete unchanged ADR-0335 child. -/
inductive LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | sixLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0336 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized six-level grouped conditional invokes exactly ADR-0336. -/
theorem elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_sixLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0335 result. -/
theorem elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for six-level-first dispatch. -/
theorem elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .sixLevelGroupedConditional boundary
        (elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | sixLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | sixLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | sixLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend
