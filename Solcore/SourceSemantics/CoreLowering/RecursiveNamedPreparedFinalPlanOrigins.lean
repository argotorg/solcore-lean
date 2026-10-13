import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning

/-! Ordinary callees discovered while preparing implementation methods retain
actual Source provenance and their final physical slot. The accepted complete
preparation pass supplies their full runtime evidence environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins
open Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning (Origin Prepared)

/-- A cached row belongs to the final preparation plan, including helpers
that were absent from the original specialization worklist. -/
theorem final_member (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) :
    row ∈ compiled.indexed.base.plan.specializations := by
  obtain ⟨actual, present, generated⟩ :=
    RecursiveNamedPreparedParameterProjections.cached_preparation compiled selected
  have actualEq : actual = row :=
    (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs generated).1.symm.trans same
  subst actual
  rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared]
  exact List.mem_reverse.mp (List.mem_of_getElem? present)

/-- Exact Source origin and an installed final row supply a prepared ordinary
caller. Its dictionary follows from the actual complete preparation receipt. -/
theorem of_cached_origin (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (origin : Origin compiled.sourceProgram row) :
    Nonempty (Prepared compiled row) := by
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ :=
    CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  have preparation := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  obtain ⟨_growth, covered⟩ := CallableCoercionPreparation.of_accepted preparation
  obtain ⟨available, resolved, _sites⟩ := covered row (final_member compiled selected same)
  exact ⟨⟨index, named, diagnostics, code, compilation, available,
    selected, same, cached, origin, resolved⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins
