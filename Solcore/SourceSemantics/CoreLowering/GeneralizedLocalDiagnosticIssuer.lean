import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaGeneration

/-! Generalized allocation retains the exact compiler diagnostic issuer and
callback. Later body failures use the actual receiving table to decode it. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDiagnosticIssuer
open Core Frontend SourceInference

/-- The original accepted named callback retains its own diagnostic inventory. -/
def Receipt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (inputs : GeneralizedLocalInstanceCompilation.Inputs) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    prepared.base.diagnostics = some issued ∧
    inputs.reasonAt = issued.program.reasonAt inputs.current.owner ∧
    ∃ own : SourceCoreProgramFaultSites.Function,
      issued.program.base.find? inputs.current.owner = some own

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDiagnosticIssuer
