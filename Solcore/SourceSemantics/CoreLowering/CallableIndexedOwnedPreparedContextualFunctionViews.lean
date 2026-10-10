import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualCellOrigins

/-! The retained prepared model has the actual existing runtime observations.
Only forward inclusion is used; observations never manufacture preparation
from a raw function type, current positive leaf or General representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFunctionViews
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualCellOrigins (functions PayloadOrigins CellOrigins)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

theorem functions_include_general :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile) := by
  intro registry mapping world sourceType source native type origin
  exact (CallableIndexedOwnedPreparedContextualCellOrigins.FunctionOrigins.forget origin).forget

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

theorem payload_general {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile
      mapping world sourceType source native type) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      mapping world sourceType source native type :=
  origin.map_functions (functions_include_general profile)

theorem cells_general {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      mapping world heap store :=
  CompatibleAmbientHeap.extend_definitions (functions_include_general profile) (.refl _) cells

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFunctionViews
