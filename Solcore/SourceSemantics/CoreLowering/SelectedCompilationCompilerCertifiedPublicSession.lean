import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial

/-! Finite checks of the complete compiled cache supply the program certificate
used by authentic public initialization. Each compiler receipt is reconstructed
inside the producer; callers retain the original checking and startup receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

variable {recipe : SourceCoreIndexedSession.Recipe}

/-- The original successful checker receipt authenticates retained method bodies.
The static profile covers all actual cached rows and original lambda nodes. -/
theorem of_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Issued recipe) := by
  obtain ⟨certificate⟩ := SelectedCompilationProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) bodies profile
  exact of_checked certificate bodies prepared member checked

/-- Real bootstrap and startup select the original entry in the automatically
issued catalog. Static profile checks replace a supplied program certificate. -/
theorem from_profile_initial_start
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
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  obtain ⟨certificate⟩ := SelectedCompilationProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) bodies profile
  exact from_initial_start checked compiled selected certificate bodies opened call
    bootstrap fresh authority ready target valid ordinaryReturn ordinaryParameters

/-- A complete eligible cached row identifies the actual first root while the
same compiler-derived certificate supplies its physical program support. -/
theorem from_profile_initial_row
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
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      initial.header.named = row.named := by
  obtain ⟨certificate⟩ := SelectedCompilationProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) bodies profile
  exact from_initial_row checked compiled selected certificate bodies opened call
    bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
