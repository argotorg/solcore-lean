import Solcore.Frontend.GroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithExpectedLambda

/-!
One opt-in group-first entry adds the one-level grouped expected-lambda path in
front of the unchanged direct-or-ordinary local-application entry.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly one grouped direct lambda as the sole call argument. -/
def isOneLevelGroupedExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .lambda _ _ _ _⟩⟩]⟩⟩ => true
  | _ => false

/-- Source-disjoint evidence retains the complete grouped child or the complete
unchanged ADR-0318 child. -/
inductive LocalApplicationWithGroupedExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | grouped {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = true)
      (elaboration : GroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch on grouped source shape before entering the unchanged ADR-0318 entry. -/
def elaborateLocalApplicationWithGroupedExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isOneLevelGroupedExpectedLambdaArgumentApplication source then
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source
  else elaborateLocalApplicationWithExpectedLambda? types owner inputs source

/-- A recognized grouped source invokes only the ADR-0319 checker. -/
theorem elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source =
      elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source := by
  simp [elaborateLocalApplicationWithGroupedExpectedLambda?, boundary]

/-- Every other source has exactly the unchanged ADR-0318 checker result. -/
theorem elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs source := by
  simp [elaborateLocalApplicationWithGroupedExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for group-first dispatch. -/
theorem elaborateLocalApplicationWithGroupedExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source =
        some (core, type) ↔
      LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithGroupedExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .grouped boundary
        (elaborateGroupedExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundary
      have boundaryFalse :
          isOneLevelGroupedExpectedLambdaArgumentApplication source = false := by
        cases equality : isOneLevelGroupedExpectedLambdaArgumentApplication source <;>
          simp_all
      exact .existing boundaryFalse
        (elaborateLocalApplicationWithExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | grouped boundary child =>
        simp [elaborateLocalApplicationWithGroupedExpectedLambda?, boundary,
          elaborateGroupedExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithGroupedExpectedLambda?, boundary,
          elaborateLocalApplicationWithExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of either selected application path. -/
theorem elaborateLocalApplicationWithGroupedExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source = none ↔
      ¬ ∃ core type, LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted :
        elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp accepted⟩)

/-- Either selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithGroupedExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | grouped boundary child => exact child.core_hasType
  | existing boundary child => exact child.core_hasType

/-- Inversion exposes the classifier result and the complete selected child. -/
theorem LocalApplicationWithGroupedExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs source core type) :
    (isOneLevelGroupedExpectedLambdaArgumentApplication source = true ∧
      GroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isOneLevelGroupedExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | grouped boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend
