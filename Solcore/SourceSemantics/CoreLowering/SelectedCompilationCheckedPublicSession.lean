import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedBodyTyping
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSession

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open SelectedCompilationPublicSessionState (StartedCall)

variable {recipe : SourceCoreIndexedSession.Recipe}

/-- Construct the automatic catalog and issuer from actual checking and the selected compiler profile. -/
theorem of_checked_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Issued recipe) := by
  exact of_profile profile (SelectedCompilationCheckedBodyTyping.of_checked checked profile)
    prepared member checked

/-- Recover a started initial entry using body typing derived from the actual checker receipt. -/
theorem from_checked_profile_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
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
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  exact from_profile_initial_start checked compiled selected profile
    (SelectedCompilationCheckedBodyTyping.of_checked checked profile) opened call bootstrap fresh authority ready
    target valid ordinaryReturn ordinaryParameters

/-- Recover a started initial cache row using body typing derived from the actual checker receipt. -/
theorem from_checked_profile_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      initial.header.named = row.named := by
  exact from_profile_initial_row checked compiled selected profile
    (SelectedCompilationCheckedBodyTyping.of_checked checked profile) opened call bootstrap fresh authority ready row

/-- Retain the actual checker receipt and profile alongside the automatic public issuer. -/
theorem profiled_of_checked_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Profiled recipe) := by
  exact profiled_of_profile profile (SelectedCompilationCheckedBodyTyping.of_checked checked profile)
    prepared member checked

/-- Recover a profiled initial entry while retaining the original checker and startup receipts. -/
theorem from_checked_profiled_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
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
  exact from_profiled_initial_start checked compiled selected profile
    (SelectedCompilationCheckedBodyTyping.of_checked checked profile) opened call bootstrap fresh authority ready
    target valid ordinaryReturn ordinaryParameters

/-- Recover a profiled initial cache row while retaining the original checker and startup receipts. -/
theorem from_checked_profiled_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
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
  exact from_profiled_initial_row checked compiled selected profile
    (SelectedCompilationCheckedBodyTyping.of_checked checked profile) opened call bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
