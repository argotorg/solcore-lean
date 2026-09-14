import Solcore.Frontend.TwoLevelGroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithGroupedExpectedLambda

/-!
One opt-in exact-depth-two-first entry adds the two-level grouped
expected-lambda path in front of the unchanged ADR-0320 entry.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly a singleton call whose argument has two groups followed
immediately by a direct lambda. -/
def isTwoLevelGroupedExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group ⟨_, .lambda _ _ _ _⟩⟩⟩]⟩⟩ => true
  | _ => false

/-- Source-disjoint evidence retains either the exact ADR0321 child or the
complete unchanged ADR0320 child. -/
inductive LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | twoLevel {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = true)
      (elaboration : TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch on the exact-depth-two source shape before entering ADR0320. -/
def elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isTwoLevelGroupedExpectedLambdaArgumentApplication source then
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source
  else elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source

/-- A recognized exact-depth-two source invokes only ADR0321. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_twoLevel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
      elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?, boundary]

/-- Every other source has exactly the unchanged ADR0320 result. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
      elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source := by
  simp [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for exact-depth-two-first dispatch. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .twoLevel boundary
        (elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundary
      have boundaryFalse :
          isTwoLevelGroupedExpectedLambdaArgumentApplication source = false := by
        cases equality : isTwoLevelGroupedExpectedLambdaArgumentApplication source <;>
          simp_all
      exact .existing boundaryFalse
        (elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | twoLevel boundary child =>
        simp [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?, boundary,
          elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?, boundary,
          elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type, LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mp accepted⟩)

/-- Either selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | twoLevel boundary child => exact child.core_hasType
  | existing boundary child => exact child.core_hasType

/-- Inversion exposes the classifier result and the complete selected child. -/
theorem LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
      types owner inputs source core type) :
    (isTwoLevelGroupedExpectedLambdaArgumentApplication source = true ∧
      TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | twoLevel boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend
