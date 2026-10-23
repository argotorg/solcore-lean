import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections
import Solcore.SourceSemantics.SourceBodyTemplateScope

/-! The actual final plan's preparation supplies a physical cache position
and the checker body for every retained row, including late-added rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources
open Frontend SourceInference SourceSpecializationWorklist
open SourceCompiledLocalFinalization

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapM_member {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} {input : α}
    (accepted : inputs.mapM action = .ok outputs) (member : input ∈ inputs) :
    ∃ output ∈ outputs, action input = .ok output := by
  induction inputs generalizing outputs with
  | nil => cases member
  | cons head tail ih =>
      rw [List.mapM_cons] at accepted
      obtain ⟨first, generated, accepted⟩ := bind_ok accepted
      obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
      cases accepted
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨first, by simp, generated⟩
      · obtain ⟨output, present, generated⟩ := ih remaining member
        exact ⟨output, by simp [present], generated⟩

theorem row_position (cached : SourceCoreUnifiedCompilation.Compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ cached.indexed.base.plan.specializations) :
    ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
      cached.indexed.base.functions[index]? = some named ∧ named.specialized = row := by
  have generated :=
    RecursiveNamedPreparedParameterProjections.automatic_functions cached.compatiblePrepared
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base cached.indexedPrepared
  rw [same] at member
  obtain ⟨named, present, accepted⟩ :=
    mapM_member generated (List.mem_reverse.mpr member)
  obtain ⟨index, position⟩ := List.mem_iff_getElem?.mp present
  refine ⟨index, named, ?_,
    (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1⟩
  rwa [same]

/-- This selects the body of the same complete row. No initial-plan membership
or independently supplied body typing is needed. -/
theorem row_selection
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ cached.indexed.base.plan.specializations) :
    ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
      cached.indexed.base.functions[index]? = some named ∧
      named.specialized = row ∧ Nonempty (BodySelection compiled row fuel) := by
  obtain ⟨index, named, position, same⟩ := row_position cached member
  obtain ⟨selected, _⟩ := SourceBodyTemplateScope.cached_selection_scope artifact checked position
  exact ⟨index, named, position, same, ⟨same ▸ selected⟩⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources
