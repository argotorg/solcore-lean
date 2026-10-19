import Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins

/-! Genuine builtin receipts enter the mixed positive function model without
changing their descriptor, native closure, or captured runtime environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

theorem included (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes
      (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world sourceType source native type related
  cases related with
  | builtin selected number descriptor typed =>
    exact .ordinary (.builtin (.prior (.prior (.builtin (.builtin selected number descriptor typed)))))

end Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueOrigins
