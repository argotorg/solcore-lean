import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins

/-! Contextual callable values expose their runtime types and identities through
the existing general representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualFunctionViews
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualCellOrigins (functions PayloadOrigins CellOrigins)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

theorem functions_include_general :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedOwnedContextualCellOrigins.FunctionOrigins.forget origin

theorem observations :
    FunctionObservations compiled.compatible.checked.catalog
      (functions headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations keys bodyRegistry faults profile
    (registry := registry) (functions_include_general profile origin)

theorem runtime_views :
    FunctionRuntimeViews (functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.runtime_views keys bodyRegistry faults profile
    (registry := registry) (functions_include_general profile origin)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualFunctionViews
