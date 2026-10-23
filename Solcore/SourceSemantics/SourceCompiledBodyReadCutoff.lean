import Solcore.SourceSemantics.SourceInferenceActualLocalReadCutoff
import Solcore.SourceSemantics.SourceCompiledActualBodyInputs

/-! The actual selected body has an empty initial node table, so the relative
read bound starts without any earlier-read premise. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem body_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program) :
    LocalReadCutoff selected.body.body.state := by
  exact CallIndex.localReadCutoff selected.inferenceCall_accepted
    (selected.inferenceCall_inputs checked) (State.initial_localBindersBelowNextLocal _ _ _)
    (by intro id impossible; cases impossible)
    (by intro node impossible; cases impossible)

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
