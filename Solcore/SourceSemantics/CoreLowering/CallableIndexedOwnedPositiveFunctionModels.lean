import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins

/-! Shared indirect prefix proofs keep their full receiving payload relation.
Only callable classification uses a forward map to the existing positive
contextual origins. Both concrete models supply this map internally. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
open Core Frontend GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The receiving model keeps the old header/registry/profile indices in
prefix interfaces while allowing any payload relation at those indices. -/
abbrev Receiving
    (_headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (_keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (_bodyRegistry : SourceCoreRawMetadata.Registry) (_faults : FunctionCalls.FaultRep)
    (_profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)

class ErasesToContextual
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop where
  erase : functions.Includes
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)

instance contextual (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    ErasesToContextual headers keys bodyRegistry faults profile
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) :=
  ⟨fun value => value⟩

instance physical (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    ErasesToContextual headers keys bodyRegistry faults profile
      (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile) :=
  ⟨CallableIndexedOwnedPhysicalCellOrigins.functions_include_contextual profile⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
