import Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart

/-! The actual bootstrap and public input encoding produce the initial mixed
heap, caller, diagnostic receiver and parameter representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialSelectedStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall)
open SelectedCompilationPublicSessionInitial (Started)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe}
  {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions} {call : StartedCall session key publicArguments options}

/-- Actual public compilation and startup recover the same recipe and selected
root before any Source execution premise is introduced. -/
theorem from_selected_call
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (opened : artifact.CompiledAt publicCompiled)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (selectRoot : ∀ root ∈ recipe.roots, root.key = key → RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
      (program := Program.ofChecked recipe.compiled.sourceProgram) (headers rows) root header) :
    Nonempty (Started rows prepared header call) := by
  obtain ⟨actualRecipe, nativeArtifact, nativeSession, checkpoint, root, world, store, native,
      encodedValues, atArtifact, _prepared, _source, atSession, atCheckpoint, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start compiled opened call.started
  have same : actualRecipe = recipe := by
    have actual := atArtifact.compiled_recipe
    cases publicCompiled
    exact Option.some.inj (actual.symm.trans selected)
  cases same
  exact ⟨{
    publicCompiled := publicCompiled, artifact := nativeArtifact, nativeSession := nativeSession,
    checkpoint := checkpoint, root := root, world := world, store := store, native := native,
    encodedValues := encodedValues, opened := atArtifact, atSession := atSession,
    atCheckpoint := atCheckpoint, started := started,
    selected := selectRoot root (List.mem_of_find?_eq_some started.selected)
      (of_decide_eq_true (List.find?_some
        (p := fun candidate : SourceCoreIndexedSession.Root recipe.compiled => decide (candidate.key = key))
        started.selected)),
    bootstrap := bootstrap, bootstrapFuel := bootstrapFuel, fresh := fresh,
    authority := authority, ready := ready }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialSelectedStart
