import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerCertifiedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryBodies

/-! Retain the original static profile and checker receipt when issuing a public
session. The same finite cache checks then supply preservation on every fault. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

structure Profiled (recipe : SourceCoreIndexedSession.Recipe) extends Issued recipe where
  staticProfile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  checked : ∃ raw checkingFuel, checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram

variable {recipe : SourceCoreIndexedSession.Recipe}

theorem Profiled.registryBodies (issued : Profiled recipe) :
    Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) := by
  obtain ⟨raw, fuel, checked⟩ := issued.checked
  exact SelectedCompilationRegistryBodies.of_profile
    (SelectedCompilationPhysicalProgramSupport.stagePrepared recipe.compiled)
    issued.support.bodyTyping checked issued.staticProfile

/-- The original successful checker receipt authenticates retained method bodies.
The static profile covers all actual cached rows and original lambda nodes. -/
theorem profiled_of_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Profiled recipe) := by
  obtain ⟨issued⟩ := of_profile profile bodies prepared member checked
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩⟩

/-- Real bootstrap and startup select the original entry in the automatically
issued catalog. Static profile checks replace a supplied program certificate. -/
theorem from_profiled_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry ⟨[]⟩ body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  obtain ⟨issued, initial, matched⟩ := from_profile_initial_start checked compiled selected
    profile bodies opened call bootstrap fresh authority ready target valid ordinaryReturn ordinaryParameters
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩, initial, matched⟩

/-- A complete eligible cached row identifies the actual first root while the
same compiler-derived certificate supplies its physical program support. -/
theorem from_profiled_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      initial.header.named = row.named := by
  obtain ⟨issued, initial, matched⟩ := from_profile_initial_row checked compiled selected
    profile bodies opened call bootstrap fresh authority ready row
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩, initial, matched⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
