import Solcore.Semantics.CheckedHostCoreProgramExecution
import Solcore.Core.HostStateSafety

/-! Admission and initial-state typing for checker-accepted host-aware Core code. -/

set_option autoImplicit false

namespace Solcore.Semantics.CheckedHostCoreProgram

/-- The fixed runtime capability environment realizes the context used by the
host checker. -/
theorem initialState_hasType
    (code : CheckedHostCoreProgram) :
    Core.HostStateHasType
      (Core.State.initial code.program.body Core.hostEnvironment)
      code.program.resultType code.program.dataDefinitions :=
  .eval .nil
    (Core.hostEnvironment_hasTypes [] code.program.dataDefinitions)
    (Core.Program.checkHost_sound code.checked) .nil

end Solcore.Semantics.CheckedHostCoreProgram
