import Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
import Solcore.SourceSemantics.SourceCompiledCachedActualBody
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSession

/-! The actual raw public compilation supplies original ordinary and method
body validity to public session issuance. Only barriers at reached inference calls and
the existing compiler profile remain explicit unfinished producer obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
open Core Frontend SourceInference
open SourceCompiledGeneralizedSoundness
open SelectedCompilationCertifiedPublicSession
open SelectedCompilationPublicSessionState (StartedCall)

variable {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
  {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem Receipt.actual_bodies (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedActualBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel) :
    SelectedCompilationBodyTyping.Bodies recipe.compiled :=
  compile_cached_bodies_of_actual_barriers receipt.compiled receipt.artifact barriers

/-- Public issuance consumes the same accepted body checks for every cached
ordinary function and implementation method. -/
theorem Receipt.actual_profiled (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedActualBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries) :
    Nonempty (Profiled recipe) :=
  profiled_of_profile profile (receipt.actual_bodies barriers) receipt.prepared member receipt.checked

/-- The real bootstrap and started call use checker-derived original body
validity. No independent body-typing or program-certificate input is needed. -/
theorem Receipt.actual_initial_row (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedActualBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel)
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
    profile (receipt.actual_bodies barriers) opened call bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
