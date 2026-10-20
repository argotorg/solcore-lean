import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts

/-! Raw public compiler success retains the exact Core compiler artifact,
checking budget and prepared recipe. Later semantic consumers use this actual
receipt instead of choosing another source compilation or checker execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
open Frontend SourceInference
open RecursiveNamedPreparedStageContracts

structure Receipt (raw : Workspace.RawWorkspace) (seeds : List SourceCompiler.Seed)
    (options : SourceCompiler.Options) (publicCompiled : SourceCompiler.Compiled)
    (recipe : SourceCoreIndexedSession.Recipe) where
  source : SourceCoreCompiler.Compiled
  compiled : SourceCoreCompiler.compile raw seeds options = .ok source
  artifact : source.artifact? = some recipe.compiled
  prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe
  publicChecked : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok publicCompiled
  selected : PublicRecipe publicCompiled recipe

theorem of_compile {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCompiler.compile raw seeds options = .ok publicCompiled)
    (selected : PublicRecipe publicCompiled recipe) :
    Nonempty (Receipt raw seeds options publicCompiled recipe) := by
  unfold SourceCoreExecution.compile at accepted
  cases sourceAccepted : SourceCoreCompiler.compile raw seeds options with
  | error error => simp [sourceAccepted, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
      simp only [sourceAccepted, Except.mapError, bind, Except.bind] at accepted
      have checked := SourceCoreCompiler.compile_checked_source sourceAccepted
      have sourceChecked : SourceCoreCompiler.compileChecked source.program seeds options = .ok source := by
        simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using sourceAccepted
      have publicChecked : SourceCompiler.compileChecked source.program seeds options = .ok publicCompiled := by
        simpa only [SourceCoreExecution.compileChecked, sourceChecked, Except.mapError, bind, Except.bind] using accepted
      obtain ⟨actual, again, artifact, prepared⟩ := public_compilation publicChecked selected
      have same : actual = source := Except.ok.inj (again.symm.trans sourceChecked)
      subst actual
      refine ⟨⟨source, sourceAccepted, artifact, prepared, ?_, selected⟩⟩
      simpa only [(source.artifact_fields artifact).1] using publicChecked

theorem Receipt.checked {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    (receipt : Receipt raw seeds options publicCompiled recipe) :
    checkProgram raw options.checkingFuel = .ok recipe.compiled.sourceProgram := by
  simpa only [(receipt.source.artifact_fields receipt.artifact).1] using
    SourceCoreCompiler.compile_checked_source receipt.compiled

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
