import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics

/-! The receiver at actual encoded input metadata is the exact diagnostic
lookup used by the pending public checkpoint. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedPublicFaultReceivers
open CallableIndexedOwnedPublicFaultReceiverTables

/-- A present genuine compiler inventory makes the table independent of the
requested entry's fallback fields. The actual input registry remains exact. -/
theorem diagnostic_eq {artifact : Artifact} {recipe : Recipe}
    (atRecipe : ArtifactRecipe artifact recipe)
    {checkpoint : Checkpoint artifact} {values : SourceCoreCompatibleValues.Context}
    (atValues : CheckpointValues checkpoint values)
    {receiver : Receiver recipe.compiled.indexed}
    (context : receiver.result.context = values)
    (issued : IssuedAt recipe.compiled.indexed receiver.entry receiver.result.context.registry
      receiver.result.extension receiver.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial recipe.compiled.compatible.checked)}
    (present : recipe.compiled.indexed.base.diagnostics = some program)
    (token : Word) :
    checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  cases checkpoint
  rename_i origin request world state stored typed extension slots actualValues owner
  change actualValues = values at atValues
  subst actualValues
  obtain ⟨base, rebuilt, table⟩ := issued
  rw [present] at rebuilt
  have registryEq : receiver.result.context.registry = values.registry := congrArg (·.registry) context
  have extensionAt : SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry values.registry := by
    rw [← owner]
    exact values.extension
  have rebuiltAt : program.tableForRegistry values.registry extensionAt = .ok base := by
    simpa only [registryEq] using rebuilt
  rw [table]
  apply Checkpoint.diagnostic_of_rebuilt
  · exact present
  · exact rebuiltAt

/-- Startup supplies the exact metadata context; the receiver producer builds
and authenticates the corresponding table without running a program. -/
theorem at_checkpoint {artifact : Artifact} {recipe : Recipe}
    (atRecipe : ArtifactRecipe artifact recipe)
    {checkpoint : Checkpoint artifact} {values : SourceCoreCompatibleValues.Context}
    (atValues : CheckpointValues checkpoint values)
    (owner : values.checked = recipe.compiled.compatible.checked)
    (entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial recipe.compiled.compatible.checked)}
    (present : recipe.compiled.indexed.base.diagnostics = some program) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry = entry ∧ receiver.result.context = values ∧
      IssuedAt recipe.compiled.indexed receiver.entry receiver.result.context.registry
        receiver.result.extension receiver.result.diagnostics ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨receiver, entryAt, contextAt, issued⟩ := Receiver.at_context recipe.compiled entry values owner
  exact ⟨receiver, entryAt, contextAt, issued, fun token =>
    diagnostic_eq atRecipe atValues contextAt issued present token⟩

/-- Actual callable preparation supplies the diagnostic inventory, so clients
need no separate presence observation. -/
theorem at_prepared_checkpoint {artifact : Artifact} {recipe : Recipe}
    (atRecipe : ArtifactRecipe artifact recipe)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (prepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled native)
    {checkpoint : Checkpoint artifact} {values : SourceCoreCompatibleValues.Context}
    (atValues : CheckpointValues checkpoint values)
    (owner : values.checked = recipe.compiled.compatible.checked)
    (entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry = entry ∧ receiver.result.context = values ∧
      IssuedAt recipe.compiled.indexed receiver.entry receiver.result.context.registry
        receiver.result.extension receiver.result.diagnostics ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨_, present, _, _⟩ := CallableIndexedOwnedPublicCallableDiagnostics.of_compiled
    recipe.compiled prepared.present
  exact at_checkpoint atRecipe atValues owner entry present

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver
