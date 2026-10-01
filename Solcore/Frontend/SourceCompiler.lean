import Solcore.Frontend.SourceCoreExecution

/-! The public source compiler is the common Core execution API. These exports
name the same compiled artifacts, values, sessions and checkpoints; no separate
compiler or execution representation is introduced here. -/
namespace Solcore.Frontend.SourceCompiler

export SourceCoreExecution
  (Seed Key Options Value Handle RunOptions CompileError Compiled
   prepare compileChecked compile compileEntryChecked compileEntry
   StaticWordRoot StaticWordProgram compileStaticWordChecked compileStaticWord
   Artifact Session Bootstrap BootResult Checkpoint Authentication Completion Outcome
   compileChecked_program compile_checked_source compileEntry_checked_source
   compileStaticWordChecked_program compileStaticWord_checked_source)

namespace Seed
export SourceCoreCompiler.Seed (declaration named)
end Seed

namespace Value
export SourceCorePublicValues.Value
  (unit bool word integer product constructed mapping proxy function type)
end Value

namespace Handle
export SourceCorePublicValues.Handle (sourceType)
end Handle

namespace Options
export SourceCoreCompiler.Options (checkingFuel specializationBudget compilationFuel)
end Options

namespace RunOptions
export SourceCoreExecution.RunOptions (inputValidationFuel executionFuel outputValidationFuel)
end RunOptions

namespace CompileError
export SourceCoreExecution.CompileError (compilation preparation discovery)
end CompileError

namespace Compiled
export SourceCoreExecution.Compiled
  (program plan roots keys rootCount root? «open» plan_validated)
end Compiled

namespace StaticWordRoot
export SourceCoreExecution.StaticWordRoot (metadata root)
end StaticWordRoot

namespace StaticWordProgram
export SourceCoreExecution.StaticWordProgram (compiled roots count rootForSelector?)
end StaticWordProgram

namespace Artifact
export SourceCoreExecution.Artifact (keys rootCount root? bootstrap)
end Artifact

namespace Bootstrap
export SourceCoreExecution.Bootstrap (resume)
end Bootstrap

namespace BootResult
export SourceCoreExecution.BootResult (ready outOfFuel error)
end BootResult

namespace Session
export SourceCoreExecution.Session
  (heapSize functionCount start startHandlePacked Authenticates authenticate
   diagnostic handleDiagnostic named builtin run invokePacked)
end Session

namespace Checkpoint
export SourceCoreExecution.Checkpoint (heapSize diagnostic resume)
end Checkpoint

namespace Authentication
export SourceCoreExecution.Authentication (typed)
end Authentication

namespace Completion
export SourceCoreExecution.Completion (value sourceType session boundaryFuel typed)
end Completion

namespace Outcome
export SourceCoreExecution.Outcome (succeeded failed outOfFuel exportError)
end Outcome

end Solcore.Frontend.SourceCompiler
