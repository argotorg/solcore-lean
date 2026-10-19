import Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry

/-! An actual named header and its selected sidecar supply the static call
authority for the corresponding invocation scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallAuthority
open Core Frontend SourceInference

def of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment}
    {program : Program}
    (header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values definitions program)
    {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      header.named.signature.key = .ok sidecar) :
    CellAwareNamedCallPorts.Authority (compiled := compiled) header.named
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
  have receipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have sourceEq : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using receipt.source issued
  exact { sidecar := sidecar
          caller := issued
          view := .inl sourceEq
          guardFrame := rfl
          unique := sourceEq ▸ header.unique }

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallAuthority
