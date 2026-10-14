import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageActualLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicInputLifting

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicProgramLifting
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPhysicalProgramSupport (Support)
open SelectedCompilationStagePublicInputLifting (NamedBodies)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}


/-- The closed induction supplies every reached named body from its authentic
compiler packet and checker-derived typing at the actual public registry. -/
theorem named_bodies (support : Support compiled (headers rows) (keys compiled) initial) :
    NamedBodies support := by
  intro receiving issued extension header member budget child selected
  exact SelectedCompilationStageNamedBodyLifting.lifts (support.bodySupport header member)
    support.profile (support.certificates header member) (SelectedCompilationPhysicalProgramSupport.static_extension support extension) selected
    (fun size _ => SelectedCompilationStageActualLifting.lifts_roots support issued extension size)
    (fun size => SelectedCompilationStageLiftBounds.preserves_roots support issued extension size)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicProgramLifting
