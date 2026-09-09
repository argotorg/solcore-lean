import Solcore.Frontend.LocalComputation
import Solcore.Frontend.LocalFunctionApplicationProperties

/-! The original child relations determine exact computation provenance.
Pure resolution cannot have a root call, so dispatch loses no old success.
No runtime inhabitant, environment alignment or store premise is involved. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem pure_dispatch {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved) :
    elaborateLocalComputation? table context source = elaborateLocalExpression? table context source := by
  cases resolution <;> rfl

theorem elaborateLocalComputation?_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalComputation? table context source = some (core, type) ↔
      LocalComputationElaborates table context source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalComputation? at accepted
    split at accepted
    · exact .application (elaborateLocalFunctionApplication?_sound accepted)
    · obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
      exact .pure resolution lowered typing
  · intro elaboration
    cases elaboration with
    | pure resolution lowered typing =>
        rw [pure_dispatch resolution]
        exact elaborateLocalExpression?_complete resolution lowered typing
    | application child =>
        have accepted := child.complete
        cases child
        exact accepted

theorem localComputationHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty} :
    LocalComputationHasType table context source type ↔
      ∃ core, LocalComputationElaborates table context source core type := by
  constructor
  · intro typing
    cases typing with
    | pure child =>
        obtain ⟨resolved, resolution, resolvedTyped⟩ := child.resolves
        obtain ⟨core, lowered, _⟩ := resolvedTyped.lowers
        exact ⟨core, .pure resolution lowered resolvedTyped⟩
    | application child =>
        obtain ⟨core, elaboration⟩ := child.elaborates_exact
        exact ⟨core, .application elaboration⟩
  · rintro ⟨core, elaboration⟩
    cases elaboration with
    | pure resolution _ typing => exact .pure (resolution.reflects_type typing)
    | application child => exact .application child.hasType

theorem LocalComputationElaborates.core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type) :
    Core.HasType context.values core type := by
  cases elaboration with
  | pure _ lowered typing => exact lowered.preserves_type typing
  | application child => exact child.core_hasType

end Solcore.Frontend
