import Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
import Solcore.SourceSemantics.SourceCompiledCachedMethodValidity
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSession

/-! The actual raw public compilation supplies original ordinary and method
body validity to public session issuance. The exact initializer barriers and
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

theorem Receipt.bodies (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel) :
    SelectedCompilationBodyTyping.Bodies recipe.compiled :=
  compile_cached_bodies_of_barriers receipt.compiled receipt.artifact barriers

/-- Public issuance consumes the same accepted body checks for every cached
ordinary function and implementation method. -/
theorem Receipt.profiled (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries) :
    Nonempty (Profiled recipe) :=
  profiled_of_profile profile (receipt.bodies barriers) receipt.prepared member receipt.checked

/-- The real bootstrap and started call use checker-derived original body
validity. No independent body-typing or program-certificate input is needed. -/
theorem Receipt.initial_row (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel)
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
    profile (receipt.bodies barriers) opened call bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
