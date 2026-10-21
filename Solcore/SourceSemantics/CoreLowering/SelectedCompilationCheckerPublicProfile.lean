import Solcore.SourceSemantics.SourceCompiledActualInitializerBarriers
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationActualCheckedPublicProfile

/-! The actual public compilation supplies checker-derived body validity and
public session issuance. The compiler profile remains a separate obligation;
initializer barriers and original-body typing are derived here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
open Core Frontend SourceInference
open SelectedCompilationCertifiedPublicSession
open SelectedCompilationPublicSessionState (StartedCall)

variable {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
  {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem Receipt.checker_bodies (receipt : Receipt raw seeds options publicCompiled recipe) :
    SelectedCompilationBodyTyping.Bodies recipe.compiled :=
  SourceCompiledActualInitializerBarriers.compile_cached_bodies receipt.compiled receipt.artifact

theorem Receipt.checker_profiled (receipt : Receipt raw seeds options publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries) :
    Nonempty (Profiled recipe) :=
  profiled_of_profile profile receipt.checker_bodies receipt.prepared member receipt.checked

/-- Real bootstrap and public call initialization consume the bodies derived
from the exact compilation receipt, without a separate initializer premise. -/
theorem Receipt.checker_initial_row (receipt : Receipt raw seeds options publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {runOptions : SourceCoreExecution.RunOptions}
    (call : StartedCall session key publicArguments runOptions)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      initial.header.named = row.named :=
  from_profiled_initial_row receipt.checked receipt.publicChecked receipt.selected
    profile receipt.checker_bodies opened call bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
